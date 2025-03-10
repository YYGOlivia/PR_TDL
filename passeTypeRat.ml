(* Module de la passe de gestion du typage *)
(* doit être conforme à l'interface Passe *)
open Tds
open Type
open Exceptions
open Ast

type t1 = Ast.AstTds.programme
type t2 = Ast.AstType.programme

(* A->id**)
let rec analyse_type_affectable a =
  match a with
  | AstTds.Ident ia ->
    begin
      match info_ast_to_info ia with
      | InfoVar (_,t,_,_) -> (t, AstType.Ident ia)
      | InfoConst _ -> (Int, AstType.Ident ia)
      | InfoFun (_,_,_) -> failwith ("Une Ident ne peut pas être un InfoFun")
      
    end

  | AstTds.Dereferencement a -> let na = analyse_type_affectable a in
                          begin
                          match na with
                          | (Pointeur t, na) -> (t, AstType.Dereferencement (na,t))
                          | _ -> failwith "erreur analyse type affecatble"
                          end


let rec est_compatible_list_params expected actual defaults =
  match expected, actual, defaults with
  | [], [], [] -> true
  | t1 :: q1, t2 :: q2, _ :: q3 -> est_compatible t1 t2 && est_compatible_list_params q1 q2 q3
  | t1 :: q1, [], Some _ :: q3 -> est_compatible_list_params q1 [] q3
  | _ -> false

(* analyse_type_appel_fonction : AstTds.AppelFonction -> typ * AstType.AppelFonction *)
let rec analyse_type_appel_fonction (AstTds.AppelFonction(info, params, lop)) =
  match info_ast_to_info info with
  | InfoFun(_, return_type, expected_params) ->
      let analysed_params = List.map analyse_type_expression params in
      let param_types = List.map fst analysed_params in
      let param_exprs = List.map snd analysed_params in
      let default_exprs = List.map (fun opt -> match opt with
        | Some exp -> Some (snd (analyse_type_expression exp))
        | None -> None) lop in
      if est_compatible_list_params expected_params param_types lop then
        let full_params = zip_params param_exprs default_exprs in
        (return_type, AstType.AppelFonction(info, full_params))
      else
        raise (TypesParametresInattendus(param_types, expected_params))
  | _ -> raise (MauvaiseUtilisationIdentifiant "fonction")

  (* construire la liste avec les params donnes et ceux par defaut *)
and zip_params given_params default_params =
  match given_params, default_params with
  | x :: xs, _ :: ys -> x :: zip_params xs ys
  | [], Some v :: ys -> v :: zip_params [] ys
  | [], [] -> []
  | _ -> failwith "Paramètres et valeurs par défaut incompatibles"


(* analyse_type_expression : AstTds.expression -> typ * AstType.expression *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie lebon typage et tranforme l'expression
en une expression de type AstType.expression *)
(* Erreur si mauvais typage *)
and analyse_type_expression e =
  match e with
  | AstTds.Booleen b -> (Bool, AstType.Booleen b)

  | AstTds.Entier n -> (Int, AstType.Entier n)

  (* Opérateurs unaires de Rat : type unaire = Numerateur | Denominateur*)
    (*Rational: Numerateur/Denominateur*)
    (* e : [x/y] -> ne : Fraction x y *)
    (* e : [x/y] -> te : Rat *)
  | AstTds.Unaire (op, e) -> 
      let (te, ne) = analyse_type_expression e in
      begin
        match op, te with
        | AstSyntax.Numerateur, Rat -> (Int, AstType.Unaire(AstType.Numerateur, ne))
        | AstSyntax.Denominateur, Rat -> (Int, AstType.Unaire(AstType.Denominateur, ne))
        | _, _ -> raise(TypeInattendu (te, Rat))
      end

  (* Opérateurs binaires existants dans Rat - résolution de la surcharge 
    type binaire = Fraction | PlusInt | PlusRat | MultInt | MultRat | EquInt | EquBool | Inf*)
    (*Vérifie les types des deux opérandes e1 et e2 et s'ils correspondent à l'opérateur op*)
  (*AstSyntax.Fraction:/*)
  (*AST exemple: AstType.Binaire(AstType.Fraction, AstType.Entier(3), AstType.Entier(2))*)
  | AstTds.Binaire (op, e1,e2) -> 
      let (te1, e1) = analyse_type_expression e1 in 
      let (te2, e2) = analyse_type_expression e2 in 
      begin
        match te1, op, te2 with
        | Int, Plus, Int -> (Int, AstType.Binaire(AstType.PlusInt, e1, e2))
        | Rat, Plus, Rat -> (Rat, AstType.Binaire(AstType.PlusRat, e1, e2))
        | Int, Mult, Int -> (Int, AstType.Binaire(AstType.MultInt, e1, e2))
        | Rat, Mult, Rat -> (Rat, AstType.Binaire(AstType.MultRat, e1, e2))
        | Bool, Equ, Bool -> (Bool, AstType.Binaire(AstType.EquBool, e1, e2))
        | Int, Equ, Int -> (Bool, AstType.Binaire(AstType.EquInt, e1, e2))
        | Int, Fraction, Int -> (Rat, AstType.Binaire(AstType.Fraction, e1, e2))
        | Int, Inf, Int -> (Bool, AstType.Binaire(AstType.Inf, e1, e2))
        | _, _, _ -> raise (TypeBinaireInattendu(op, te1, te2))
      end

      | AstTds.AppelFonction(info, le, lop) ->
        let list_aux = List.map analyse_type_expression le in
        let list_expr = List.map (fun (_, y) -> y) list_aux in
        let list_typ = List.map (fun (x, _) -> x) list_aux in
        begin
          match info_ast_to_info info with
          | InfoFun(_, te, lt) ->
              if est_compatible_list lt list_typ then
                (te, AstType.AppelFonction(info, list_expr))
              else 
                raise (TypesParametresInattendus (list_typ, lt))
          | _ -> failwith "Erreur appel fonction"
        end

    (*type info =
    | InfoVar of string * typ * int * string
    | InfoConst of string * int
    | InfoFun of string * typ * typ list*)
    (*E->A*)
  | AstTds.Affectable a -> 
      let (t, na) = analyse_type_affectable a in 
      (t, AstType.Affectable na)

  (* Dans le cas d'un pointeur nul, on va renvoyer également son type qui est indéfini pour le moment. *)
  | AstTds.Null -> (Pointeur Undefined, AstType.Null)

  | AstTds.New t -> (Pointeur t, AstType.New t)

  | AstTds.Adresse ia -> 
      begin
        match info_ast_to_info ia with
        | InfoVar(_, t, _, _) -> (Pointeur t, AstType.Adresse ia)
        | InfoConst _ -> (Pointeur Int, AstType.Adresse ia)
        | _ -> failwith "Erreur adresse"
      end

  



(* analyse_type_instruction : AstTds.instruction -> AstType.instruction )
( Paramètre i : l'instruction à analyser )
( Vérifie le typage et tranforme l'instruction AstTds.instruction
en une instruction de type AstType.instruction )
( Erreur si mauvais typage *)
let rec analyse_type_instruction i =
  match i with
  | AstTds.Declaration (t, ia, e) ->
      
    let (te, ne) = analyse_type_expression e in
    if (Type.est_compatible te t) then 
      begin
      Tds.modifier_type_variable t ia;
      AstType.Declaration(ia, ne)
      end
    else 
      raise (TypeInattendu(te,t))
        
(*I->A=E*)
(*Verifier left et right*)
(*left:analyse_type_affectable*)
(*right:analyse_type_expression *)
(*ne:nouveu expression*) (*na:nouveu affectable*)
(*te:type de expression*)
(*ta:type de affectable*)
(*val est_compatible : typ -> typ -> bool*)
| AstTds.Affectation(a, e) -> 

      let (te, ne) = analyse_type_expression (e) in 
      let (ta, na) = analyse_type_affectable (a) in

      if est_compatible ta te then 
        AstType.Affectation(na,ne)

      else 
        raise (TypeInattendu(te,ta))



    | AstTds.Affichage(e) ->
      let (te, ne) = analyse_type_expression e in

      (* Ici, on peut avoir des pointeurs de pointeurs de pointeurs etc. *)
      (* Donc il nous faut pouvoir avoir une forme de récursivité. *)
      let rec analyse_type_pointeur t =
      match t with
      | Int -> AstType.AffichageInt(ne)
      | Rat -> AstType.AffichageRat(ne)
      | Bool -> AstType.AffichageBool(ne)
      | Pointeur t' -> analyse_type_pointeur t'
      | Undefined -> failwith "Type non défini"
      in
      begin
      match te with
      | Int -> AstType.AffichageInt(ne)
      | Rat -> AstType.AffichageRat(ne)
      | Bool -> AstType.AffichageBool(ne)
      | Pointeur t -> analyse_type_pointeur t
      | Undefined -> failwith "Type non défini"
      end


     
  | AstTds.Conditionnelle (e,b1,b2) ->
      let (te,ne) = analyse_type_expression e in 
      let nb1 = analyse_type_bloc b1 in 
      let nb2 = analyse_type_bloc b2 in
      
      if Type.est_compatible Bool te then 
        AstType.Conditionnelle(ne,nb1,nb2)
      else 
        raise (TypeInattendu (te,Bool))

  | AstTds.TantQue (e,b) ->
    let (te,ne) = analyse_type_expression e in 
    let nb = analyse_type_bloc b in 
    
    if Type.est_compatible Bool te then 
      AstType.TantQue(ne,nb)
    else 
      raise (TypeInattendu (te,Bool))

      

  | AstTds.Retour (e,ia) -> 
    let (te,ne) = analyse_type_expression e in 
    begin
    match info_ast_to_info ia with 
          | InfoFun (_,tr,_) -> 
                                if (Type.est_compatible te tr) then 

                                  AstType.Retour(ne, ia)
                                
                                else 
                                  raise (TypeInattendu(te,tr))

          | _ -> failwith "Retour erreur"
    end

  | AstTds.Empty -> AstType.Empty

  | DeclarationStatique (t, i, e) -> 
    let (te, ne) = analyse_type_expression e in
    if (est_compatible te t) then
      AstType.DeclarationStatique(i, ne)
    else 
      raise (TypeInattendu (te, t))
  

      
  

(* analyse_type_bloc : AstTds.bloc ->AstType.bloc *)
(* Paramètre li : liste d'instructions à analyser *)
(* Erreur si mauvais type *)
and analyse_type_bloc li =
  List.map (analyse_type_instruction) li 






(* analyse_type_parametre : (typ * info_ast) list -> info_ast list *)
(* Paramètre l : liste de paramètres à analyser *)
(* Renvoie la liste des informations des paramètres *)
(* Erreur si mauvais type *)
(*ex: lp = [(Int, info1); (Rat, info2); (Bool, info3)]*)
let rec analyse_type_parametre l =
      match l with
      | [] -> []
      | (t,info)::q ->
          match (info_ast_to_info info) with
          | InfoConst _ -> 
            if (est_compatible Int t) then
            info::analyse_type_parametre(q)
            else 
              raise (TypeInattendu (Int, t))
          | InfoVar(_,t_info,_,_) -> 
            begin
              if (est_compatible t_info t) then
              info::analyse_type_parametre(q)
              else
                raise (TypeInattendu(t_info, t))
              end
          | _ -> failwith "Uniquement InfoConst et InfoVar attendus"

  (*AstTds.fonction -> AstType.fonction*)
  (*t:type de retours de Fonction*)
  (*info: info_ast*)
  (*lp:liste de paramètre (type,info_ast)list*)
  (*li:liste de instruction*)
  let rec analyse_type_fonction (AstTds.Fonction(_, info, lp, li)) =
    (*Mettre à jour info*)
    (*t a été enregistré dans info*)
    (*list.map fst lp: le premier élément dans chaque liste dans lp  *)
    (*ex: lp = [(Int, info1); (Rat, info2); (Bool, info3)]*)
    (*list.map fst lp: [Int, Rat, Bool]*)
    (*modifier_type_fonction t (List.map(fst) lp) info; (*modifier_type_fonction?*)*)
    let filtered_lp = List.map (fun (t, info, _) -> (t, info)) lp in
    let nlp = analyse_type_parametre filtered_lp in
    let nli = analyse_type_bloc li in
    AstType.Fonction(info, nlp, nli)

    and analyse_type_fonctions lf =
      List.map(analyse_type_fonction) lf
 
  (* analyse_type_var : AstTds.declaration -> AstType.declaration *)
(* Paramètre v : la déclaration à analyser *)
(* Vérifie le typage et transforme la déclaration AstTds.declaration *)
let analyse_type_var v =
  match v with
  | AstTds.DeclarationStatique(t, i, e) -> 
    let (te, ne) = analyse_type_expression e in
    if (est_compatible te t) then
      (* On n'a plus besoin des types puisque la compatibilité a été vérifiée dans cette passe *)
      AstType.DeclarationStatique(i, ne)
    else 
      raise (TypeInattendu (te, t))

  (*AstTds.programme -> AstType.programme*)
  (*fonctions:AstTds.fonction list*)
  (*nf: AstType.fonction list*)
  (*prog: AstTds.bloc*)
  (*nb: AstType.bloc*)
  let analyser(AstTds.Programme(vars,fonctions,prog)) = 
  (*list.map: Appliquer analyser_type_fonction à chaque fonction  *)
  (*analyse_type_fonction: AstTds.fonction list -> AstType.fonction  list*)
  let nv = List.map (analyse_type_var) vars in
  let nf = List.map(analyse_type_fonction) fonctions in
  let nb = analyse_type_bloc prog in
  AstType.Programme(nv,nf,nb)

    