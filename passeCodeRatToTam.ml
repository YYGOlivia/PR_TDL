open Tds
open Type
open Ast
open Tam
open Code 

type t1 = Ast.AstPlacement.programme
type t2 = string



(*A->id*)
(*store: Affectation*)
(*load : Calcul*)
(*x=3 id_left = true --->Tam.store*)
(*x+1 id_left = false --->Tam.load *)
(*InfoConst->pas besoin*)
let rec analyse_code_affectable a is_left = 
  match a with 
  | AstType.Ident ia ->
    begin
      match info_ast_to_info ia with 
      | InfoVar (_,t,d,r) -> if is_left then Tam.store (getTaille t) d r 
                                else Tam.load (getTaille t) d r
      | InfoConst (_,i) -> Tam.loadl_int i
      | _ -> failwith "erreur analyse type expression infovar"
    end

    | AstType.Dereferencement (a,t) -> 
      if is_left then (analyse_code_affectable a false) ^ (Tam.storei (getTaille t)) 
      else (analyse_code_affectable a false) ^ Tam.loadi (getTaille t)

    
  
                              

                              
(* analyse_code_expression : AstPlacement.expression -> string *)
(* Paramètre e : l'expression à analyser *)
(* Transforme l'expression en langage de la machine TAM *)
let rec analyse_code_expression e = 
  match e with 

  (*E->A*)
  (*E:y = x + 1*)
  (*x est affectable(A) mais x is_left = false*)
  (*A:is_left = false*)
  | AstType.Affectable (a) -> 
    analyse_code_affectable a false

  | Null -> loadl_int 0

  | New t -> (loadl_int (getTaille t))^(subr "MAlloc")

  | Adresse ia ->
    begin
      match info_ast_to_info ia with
        | InfoVar(_,_,d,r) -> loada d r
        | _ -> failwith "error analyse_code_exp Adresse"
    end

    | AstType.Booleen b -> 
      (* Génère le code TAM pour une constante booléenne *)
      if b then 
        loadl_int 1 
      else 
        loadl_int 0

  | AstType.Entier n -> loadl_int n

  | AstType.Unaire (op, e1) ->    
    (* Génère le code TAM pour une opération unaire *)
    analyse_code_expression e1 ^
      begin
        match op with
        | AstType.Numerateur -> Tam.pop(0) 1
        | AstType.Denominateur -> Tam.pop(1) 1
      end


  | AstType.Binaire (op, e1, e2) ->
    analyse_code_expression e1 ^ 
    analyse_code_expression e2 ^
    begin
      match op with
      | Fraction -> "" (* On veut juste avoir un Rat donc c'est déjà fait dans les deux analyses *)
      | PlusInt -> Tam.subr "IAdd"
      | PlusRat -> Tam.call "ST" "RAdd"
      | MultInt -> Tam.subr "IMul"
      | MultRat -> Tam.call "ST" "RMul"
      | EquInt -> Tam.subr "IEq"
      | EquBool -> Tam.subr "IEq" (* Car deux entiers *)
      | Inf -> Tam.subr "ILss"
    end

    | AstType.AppelFonction (info, le) ->
      let code_args = 
        List.fold_left (fun acc e -> acc ^ analyse_code_expression e) "" le
      in
      begin
        match info_ast_to_info info with
        | InfoFun(n, _, _) ->
          code_args ^ Tam.call "SB" n
        | _ -> failwith "Ce n'est pas une InfoFun dans un appel de fonction"
      end
  




(* analyse_code_instruction : AstPlacement.instruction -> string *)
(* Paramètre i : l'instruction à analyser *)
(* Transforme l'instruction en langage de la machine TAM *)
let rec analyse_code_instruction i =
  match i with
  | AstPlacement.Declaration (info, e) ->
    (* Génère le code TAM pour une déclaration de variable *)
    begin
      match info_ast_to_info info with
      | InfoVar (_,t,depl,reg) -> 
        let tt = getTaille t in
        (Tam.push tt) ^ (analyse_code_expression e) ^ (Tam.store (tt) depl reg)
      | _ -> failwith "Pas une InfoVar dans une déclaration"
    end


    (*I->A=E*)
    (*affectation(left)=expression(right)*)
  | AstPlacement.Affectation (a,e) ->
    let code_exp = analyse_code_expression e in
    let code_aff = analyse_code_affectable a true in
    code_exp^code_aff

  
  | AstPlacement.AffichageInt e -> 
    (* Génère le code TAM pour l'affichage d'un entier *)
    (analyse_code_expression e) ^ Tam.subr "IOut"

  | AstPlacement.AffichageRat e -> 
    (* Génère le code TAM pour l'affichage d'un rationnel *)
    (analyse_code_expression e) ^ Tam.call "ST" "ROut" 

  | AstPlacement.AffichageBool e ->
    (* Génère le code TAM pour l'affichage d'un booléen *)
    (analyse_code_expression e) ^ Tam.subr "BOut"

  | AstPlacement.Conditionnelle (c, t, e) ->
    (* Génère le code TAM pour une structure conditionnelle *)
    let elseEtiquette = getEtiquette() in
    let finSiEtiquette = getEtiquette() in
    (analyse_code_expression c) ^
    Tam.jumpif (0) elseEtiquette ^
    (analyse_code_bloc t) ^
    Tam.jump finSiEtiquette ^
    Tam.label elseEtiquette ^
    (analyse_code_bloc e) ^
    Tam.label finSiEtiquette
      


  | AstPlacement.TantQue (c,b) ->
    (* Génère le code TAM pour une boucle while *)
    let debutTQEtiquette = getEtiquette() in
    let finTQEtiquette = getEtiquette() in
    Tam.label debutTQEtiquette ^
    (analyse_code_expression c) ^
    Tam.jumpif (0) finTQEtiquette ^
    (analyse_code_bloc b) ^
    Tam.jump debutTQEtiquette ^
    Tam.label finTQEtiquette

  

  | AstPlacement.Retour (e, tailleRet, tailleParam) ->
    (* Génère le code TAM pour une instruction de retour de fonction *)
    (analyse_code_expression e) ^ Tam.return (tailleRet) (tailleParam)

  | AstPlacement.Empty -> ""

  | DeclarationStatique (i,e) ->  
    begin
      match info_ast_to_info i with 
      | InfoVar(_,t,d,r) -> 
        let taille_t = getTaille t in
        (Tam.push taille_t) ^ (analyse_code_expression e) ^ (Tam.store (taille_t) d r)
      | _ -> failwith "Ce n'est pas une InfoVar dans la déclaration"
    end

(* analyse_code_bloc : AstPlacement.bloc -> string *)
(* Analyse un bloc d'instructions et génère le code TAM correspondant. *)
(* Paramètre li : la liste des instructions du bloc *)
(* Paramètre taille : la taille du bloc *)
(* Retour : le code TAM généré pour le bloc *)
and analyse_code_bloc (li, taille) =
  (List.fold_left(fun acc i -> acc ^ (analyse_code_instruction i)) "" li) ^
  Tam.pop 0 taille  


(* analyse_code_var : AstPlacement.var -> string *)
let analyse_code_var v = 
  match v with 
  | AstPlacement.DeclarationStatique(info, e) -> 
    begin
      match info_ast_to_info info with 
      | InfoVar(_,t,d,r) -> 
        let taille_t = getTaille t in
        (Tam.push taille_t) ^ (analyse_code_expression e) ^ (Tam.store (taille_t) d r)
      | _ -> failwith "Ce n'est pas une InfoVar dans la déclaration"
    end

(* analyse_code_fonction : AstPlacement.fonction -> string *)
(* Analyse une fonction et génère le code TAM correspondant. *)
(* Paramètre f : la fonction à analyser *)
(* Retour : le code TAM généré pour la fonction *)

(* analyse_code_fonction : AstPlacement.fonction -> string *)
(* Analyse une fonction et génère le code TAM correspondant. *)
(* Paramètre f : la fonction à analyser *)
(* Retour : le code TAM généré pour la fonction *)
let analyse_code_fonction (AstPlacement.Fonction(info, _, (li, _))) =
  match info_ast_to_info info with 
    | InfoFun(n, _, _) -> 
      Tam.label n ^
      analyse_code_bloc (li, 0) ^ Tam.halt
    | _ -> "Pas une InfoFun dans une fonction" 

  

(* analyser : AstPlacement.programme -> string *)
(* Analyse un programme et génère le code TAM correspondant. *)
(* Paramètre p : le programme à analyser *)
(* Retour : le code TAM généré pour le programme *)
let analyser (AstPlacement.Programme(lv,lf,b)) =
  let entete = getEntete() in
  let nlv = List.fold_left(fun acc v -> acc ^ (analyse_code_var v)) "" lv in
  let nf = List.fold_left(fun acc f -> acc ^ (analyse_code_fonction f))"" lf in
  let nb = analyse_code_bloc b in
  entete ^ nlv ^ nf ^ Tam.label "main" ^ nb ^ Tam.halt