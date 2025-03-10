open Ast
open Tds
open Type

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme

(*pas besoin *)
(*let analyse_placement_affectable a = AstType.Affectable(a)*)

(* analyse_placement_expression : AstType.expression -> AstPlacement.expression *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie le placement et transforme l'expression 
  en une expression de type AstPlacement.expression *)
(* Erreur si mauvais placement *)
let analyse_placement_expression e = e

(* analyse_placement_instruction : AstType.instruction -> int -> string -> AstPlacement.instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Paramètre depl : le déplacement courant *)
(* Paramètre reg : le registre courant *)
(* Vérifie le placement et transforme l'instruction AstType.instruction
  en une instruction de type AstPlacement.instruction *)
(* Erreur si mauvais placement *)
let rec analyse_placement_instruction i depl reg =
  match i with
  | AstType.Declaration (info, e) ->
   begin
    (* Modifier l'adresse de la variable *)
    modifier_adresse_variable depl reg info;
    let taille =
      match info_ast_to_info info with
      | InfoVar(_, t, _, _) -> getTaille t
      | _ -> 0
    in
    (AstPlacement.Declaration(info, e), taille)
   end

  | AstType.Conditionnelle(c, t, e) ->
   let nbt = analyse_placement_bloc t depl reg in
   let nbe = analyse_placement_bloc e depl reg in
   (AstPlacement.Conditionnelle(c, nbt, nbe), 0)
   
  | AstType.TantQue(c, b) ->
   let nb = analyse_placement_bloc b depl reg in
   (AstPlacement.TantQue(c, nb), 0)

  | AstType.Retour(e, info) ->
   begin
    match (info_ast_to_info info) with
    | InfoFun(_, tr, tl) -> 
      (* Récupérer le type de retour dans l'info *)
      let trt = getTaille tr in
      (* Récupérer la liste de types de paramètres *)
      let tlt = getTailleListe tl in
      (AstPlacement.Retour(e, trt, tlt), 0)
    | _ -> failwith "Pas une InfoFun en retour d'une fonction"
   end

  | AstType.Affectation(a, e) -> (AstPlacement.Affectation(a, e), 0)
  
  | AstType.AffichageInt(e) -> (AstPlacement.AffichageInt(e), 0)

  | AstType.AffichageRat(e) -> (AstPlacement.AffichageRat(e), 0)

  | AstType.AffichageBool(e) -> (AstPlacement.AffichageBool(e), 0)

  | AstType.Empty -> (AstPlacement.Empty, 0)

  | AstType.DeclarationStatique (info, e) ->     
    (* On va procéder de la même manière que pour une variable classique *)
    begin
      modifier_adresse_variable depl reg info;
      let taille =
        match info_ast_to_info info with
        | InfoVar(_, t, _, _) -> getTaille t
        | _ -> 0
      in
      (AstPlacement.Declaration(info, e), taille)
   end

(* analyse_placement_bloc : AstType.instruction list -> int -> string -> AstPlacement.instruction list * int *)
(* Paramètre li : la liste d'instructions à analyser *)
(* Paramètre depl : le déplacement courant *)
(* Paramètre reg : le registre courant *)
(* Vérifie le placement et transforme la liste d'instructions AstType.instruction
  en une liste d'instructions de type AstPlacement.instruction *)
(* Erreur si mauvais placement *)
and analyse_placement_bloc li depl reg =
  match li with
  | [] -> ([], 0)
  | i :: q -> 
   let (ni, ti) = analyse_placement_instruction i depl reg in
   let (nq, tq) = analyse_placement_bloc q (depl + ti) reg in
   (ni :: nq, ti + tq)

(* analyse_placement_parametre : AstType.parametre list -> int -> string -> AstType.parametre list *)
(* Paramètre lp : la liste de paramètres à analyser *)
(* Paramètre depl : le déplacement courant *)
(* Paramètre reg : le registre courant *)
(* Vérifie le placement et transforme la liste de paramètres AstType.parametre
  en une liste de paramètres de type AstType.parametre *)
(* Erreur si mauvais placement *)
let rec analyse_placement_parametre lp depl reg =
  match lp with
  | [] -> []
  | i :: q -> 
   begin
    match info_ast_to_info i with
    | InfoVar(_, t, _, _) -> 
      let ti = getTaille t in
      let ndepl = depl - ti in
      modifier_adresse_variable ndepl reg i;
      i :: (analyse_placement_parametre q ndepl reg)
    | _ -> failwith "Pas une InfoVar en paramètre d'une fonction"
   end

(* analyse_placement_var : AstType.var -> AstPlacement.var *)
(* Paramètre v : la variable à analyser *)
(* Vérifie le placement et transforme la variable AstType.var
  en une variable de type AstPlacement.var *)
(* Erreur si mauvais placement *)
let analyse_placement_var v = 
  match v with
  | AstType.DeclarationStatique(info, e) -> AstPlacement.DeclarationStatique(info, e)

(* analyse_placement_fonction : AstType.fonction -> AstPlacement.fonction *)
(* Paramètre f : la fonction à analyser *)
(* Vérifie le placement et transforme la fonction AstType.fonction
  en une fonction de type AstPlacement.fonction *)
(* Erreur si mauvais placement *)

(* analyse_placement_fonction : AstType.fonction -> AstPlacement.fonction *)
(* Paramètre f : la fonction à analyser *)
(* Vérifie le placement et transforme la fonction AstType.fonction
  en une fonction de type AstPlacement.fonction *)
(* Erreur si mauvais placement *)
let analyse_placement_fonction (AstType.Fonction(info, lp, li)) = 
  let nlp = analyse_placement_parametre (List.rev lp) 0 "LB" in
  let nli = analyse_placement_bloc li 3 "LB" in
  AstPlacement.Fonction(info, nlp, nli)

(* analyser : AstType.programme -> AstPlacement.programme *)
(* Paramètre p : le programme à analyser *)
(* Vérifie le placement et transforme le programme AstType.programme
  en un programme de type AstPlacement.programme *)
(* Erreur si mauvais placement *)
let analyser (AstType.Programme(lv,lf, b)) = 
  let nlv = List.map analyse_placement_var lv in
  let nlf = List.map analyse_placement_fonction lf in
  let nb = analyse_placement_bloc b 0 "SB" in
  AstPlacement.Programme(nlv,nlf, nb)
