open Tds
open Exceptions
open Ast
open Tdp

type t1 = Ast.AstSyntax.programme
type t2 = Ast.AstTds.programme


(* List.mapi : (int -> 'a -> 'b) -> 'a list -> 'b list *)

let rec analyse_appel_fonction tds tdp (AstSyntax.AppelFonction (nom, params)) =
  (* Chercher globalement dans la table des symboles le nom de la fonction appelée *)
  match Tds.chercherGlobalement tds nom with
  | Some ast_info -> (
      (* Si trouvé, convertir l'information AST en information de type (pour fonctions/variables) *)
      match info_ast_to_info ast_info with
      | InfoFun (nom_fun, _, _) ->
          (* Analyser chaque paramètre de l'appel de fonction *)
          let analysed_params = List.map (analyse_tds_expression tds tdp) params in
          (* Trouver les paramètres par défaut pour la fonction appelée dans la table de paramètres par défaut *)
          (match Hashtbl.find_opt tdp nom_fun with
          | Some lprms -> 
            (* Si des paramètres par défaut existent, construire un noeud d'appel de fonction avec les paramètres analysés et les paramètres par défaut *)
            AstTds.AppelFonction (ast_info, analysed_params, lprms)
          | None -> 
            (* Si aucun paramètre par défaut n'est trouvé et que la fonction nécessite des paramètres par défaut, lever une exception *)
            raise (Exceptions.MauvaiseUtilisationIdentifiant nom_fun))
      | InfoConst _ | InfoVar _ -> 
        (* Lever une exception si le nom trouvé ne correspond pas à une fonction mais à une constante ou une variable *)
        raise (Exceptions.MauvaiseUtilisationIdentifiant nom))
  | None -> 
    (* Lever une exception si aucun symbole correspondant au nom de la fonction n'est trouvé dans la table des symboles globale *)
    raise (Exceptions.UndefinedFunction nom)

(* analyse_tds_affectable : tds -> AstSyntax.affectable -> bool -> AstTds.affectable *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre a : l'affectable à analyser *)
(* Paramètre is_left : true si l'affectable est à gauche d'une affectation, false sinon *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'affectable *)
and analyse_tds_affectable tds a is_left =
  match a with
  | AstSyntax.Ident n -> 
    begin
      match (chercherGlobalement tds n) with
      | None -> raise (IdentifiantNonDeclare n) 
      | Some info -> 
        begin
          match info_ast_to_info info with 
          (*int x; x est un variable
            x=5;  x est affectable*)
            | InfoVar _-> AstTds.Ident(info) (*change pas*)
            (*const x=5->x est un constant*)
            (*is_left = true x peut pas etre affectable prsq x est un constant*)
            | InfoConst _ -> if is_left then raise (MauvaiseUtilisationIdentifiant n) else AstTds.Ident info
            | InfoFun _ -> raise (MauvaiseUtilisationIdentifiant n)
        end
    end
  | AstSyntax.Dereferencement a -> AstTds.Dereferencement(analyse_tds_affectable tds a is_left)



(* analyse_tds_expression : tds -> AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_expression tds tdp e = 
  match e with
  | AstSyntax.AppelFonction (id, le) ->
    begin
      match chercherGlobalement tds id with
      | None ->
          raise (IdentifiantNonDeclare id)
      | Some info -> 
        begin
          match info_ast_to_info info with 
          | InfoFun _ ->
              let nle = List.map (analyse_tds_expression tds tdp) le in
              let default_params_opt = Hashtbl.find_opt tdp id in
              let default_params = match default_params_opt with
                | Some params -> params  (* Utiliser les paramètres par défaut, le cas échéant *)
                | None -> []              (* Si aucun paramètre par défaut n'est trouvé, une liste vide est utilisée *)
              in
              AstTds.AppelFonction(info, nle, default_params) (* Ici je ne sais pas je dois prendre en compte les variables globales déjà définies *)
          | _ -> 
              raise (MauvaiseUtilisationIdentifiant id)
        end
    end

     (* E->A *)
  | AstSyntax.Affectable a -> 
    AstTds.Affectable (analyse_tds_affectable tds a false)


  |AstSyntax.Binaire(b, e1, e2) -> 
    begin
      let ne1 = analyse_tds_expression tds tdp e1 in
      let ne2 = analyse_tds_expression tds tdp e2 in
        AstTds.Binaire(b, ne1, ne2)
    end

  |AstSyntax.Unaire(u, e) -> 
    begin
      let ne = analyse_tds_expression tds tdp e in  
      AstTds.Unaire(u, ne)
    end

  | AstSyntax.Entier n -> AstTds.Entier n

  | AstSyntax.Booleen b -> AstTds.Booleen b
  
  | AstSyntax.Null -> AstTds.Null
  
  | AstSyntax.New t -> AstTds.New t

  | AstSyntax.Adresse n -> (
      match chercherGlobalement tds n with
      | None -> raise (IdentifiantNonDeclare n)
      | Some info -> (
          match info_ast_to_info info with
          | InfoVar _ -> AstTds.Adresse info
          (* Dans le cas où on a autre chose qu'une InfoVar alors on ne peut pas en prendre l'adresse *)
          | _ -> raise (MauvaiseUtilisationIdentifiant n)))
    


(* analyse_tds_instruction : tds -> info_ast option -> AstSyntax.instruction -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si l'instruction i est dans le bloc principal,
                   Some ia où ia est l'information associée à la fonction dans laquelle est l'instruction i sinon *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds tdp oia i =
  match i with
  | AstSyntax.Declaration (t, n, e) ->
      begin
        match chercherLocalement tds n with
        | None ->
            (* L'identifiant n'est pas trouvé dans la tds locale,
            il n'a donc pas été déclaré dans le bloc courant *)
            (* Vérification de la bonne utilisation des identifiants dans l'expression *)
            (* et obtention de l'expression transformée *)
            let ne = analyse_tds_expression tds tdp e in
            (* Création de l'information associée à l'identfiant *)
            let info = InfoVar (n,Undefined, 0, "") in
            (* Création du pointeur sur l'information *)
            let ia = info_to_info_ast info in
            (* Ajout de l'information (pointeur) dans la tds *)
            ajouter tds n ia;
            (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information
            et l'expression remplacée par l'expression issue de l'analyse *)
            AstTds.Declaration (t, ia, ne)
        | Some _ ->
            (* L'identifiant est trouvé dans la tds locale,
            il a donc déjà été déclaré dans le bloc courant *)
            raise (DoubleDeclaration n)
      end

      (*I->A=E*)  
      (*x=i+2*)
      (*af:x*)
      (*ne:i+2*)
  | AstSyntax.Affectation (a, e) ->
    let na = analyse_tds_affectable tds a true in
    (* Vérification de la bonne utilisation des identifiants dans l'expression *)
    (* et obtention de l'expression transformée *)
    let ne = analyse_tds_expression tds tdp e in

    (* Renvoie de la nouvelle affectation où le nom a été remplacé par l'information
        et l'expression remplacée par l'expression issue de l'analyse *)
    AstTds.Affectation (na, ne)
    
  | AstSyntax.Constante (n,v) ->
      begin
        match chercherLocalement tds n with
        | None ->
          (* L'identifiant n'est pas trouvé dans la tds locale,
             il n'a donc pas été déclaré dans le bloc courant *)
          (* Ajout dans la tds de la constante *)
          ajouter tds n (info_to_info_ast (InfoConst (n,v)));
          (* Suppression du noeud de déclaration des constantes devenu inutile *)
          AstTds.Empty
        | Some _ ->
          (* L'identifiant est trouvé dans la tds locale,
          il a donc déjà été déclaré dans le bloc courant *)
          raise (DoubleDeclaration n)
      end

  | AstSyntax.Affichage e ->
      let ne = analyse_tds_expression tds tdp e in

      AstTds.Affichage (ne)
  | AstSyntax.Conditionnelle (c,t,e) ->
      let nc = analyse_tds_expression tds tdp c in
      let tast = analyse_tds_bloc tds tdp oia t in
      let east = analyse_tds_bloc tds tdp oia e in
      AstTds.Conditionnelle (nc, tast, east)

  | AstSyntax.TantQue (c,b) ->
      let nc = analyse_tds_expression tds tdp c in
      let bast = analyse_tds_bloc tds tdp oia b in
      AstTds.TantQue (nc, bast)

  | AstSyntax.Retour (e) ->
      begin
        match oia with
        | None -> raise RetourDansMain
        | Some ia ->
            let ne = analyse_tds_expression tds tdp e in
            AstTds.Retour (ne, ia)
      end

    
  | AstSyntax.DeclarationStatique (t,n,e) -> 
    begin
      (* On cherche localement puisqu'elles ont une portée locale 
      et qu'une variable locale à une fonciton ne doit pas interférer avec 
      les variables d'autres fonctions ou bien avec les variables globales *)
      match chercherLocalement tds n with
      | None -> 
        let ne = (analyse_tds_expression tds tdp e) in
        let info = InfoVar (n,t,0,"") in
        let info_ast = info_to_info_ast info in
        ajouter tds n info_ast;
        AstTds.DeclarationStatique(t,info_ast,ne)
      | Some _ -> raise (DoubleDeclaration n)
    end


(* analyse_tds_bloc : tds -> info_ast option -> AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si le bloc li est dans le programme principal,
                   Some ia où ia est l'information associée à la fonction dans laquelle est le bloc li sinon *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_bloc tds tdp oia li =
  let tdsbloc = creerTDSFille tds in
  let nli = List.map (analyse_tds_instruction tdsbloc tdp oia) li in
  nli

(* analyse_liste_param : tds -> (typ * string * expression option) list -> (typ * info_ast * expression option) list *)
(* Ajoute les paramètres à la TDS et retourne la liste avec info_ast *)
(*vop :valeur optionnelle de paramètre*)
let rec analyse_liste_param tds l =
  match l with
  | [] -> []
  | (t, n, vop)::q ->
      match chercherLocalement tds n with
      | None ->
          let info_param = Tds.InfoVar(n, t, 0, "") in
          let info_ast = info_to_info_ast info_param in
          ajouter tds n info_ast;
          (t, info_ast, vop)::analyse_liste_param tds q
      | Some _ -> raise (DoubleDeclaration n)

(* analyse_tds_fonction : tds -> AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* analyse_tds_fonction : tds -> AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
let analyse_tds_fonction maintds tdp (AstSyntax.Fonction (t, n, lp, li)) =
  (* Vérification si la fonction est déjà définie dans la portée locale *)
  match chercherLocalement maintds n with
  | Some _ -> raise (DoubleDeclaration n)  (* Exception si double déclaration *)
  | None -> 
    (* Enregistrement des informations de la fonction avec les types des paramètres *)
    let param_types = List.map (fun (t, _, _) -> t) lp in
    let info_fun = Tds.InfoFun (n, t, param_types) in
    let info_fun_ast = info_to_info_ast info_fun in
    ajouter maintds n info_fun_ast;  (* Ajout de la fonction dans la TDS *)

    (* Vérification de la double déclaration dans les paramètres *)
    let param_names = List.map (fun (_, n, _) -> n) lp in
    let rec check_duplicates names =
      match names with
      | [] -> ()
      | x :: xs ->
        if List.mem x xs then raise (DoubleDeclaration x)  (* Détection de doublons *)
        else check_duplicates xs
    in
    check_duplicates param_names;

    (* Création d'une nouvelle TDS pour les paramètres de la fonction *)
    let tds_fille = creerTDSFille maintds in
    let nlp_converted = List.map (fun (t, n, vop) ->
      let info_ast = 
        match chercherLocalement tds_fille n with
        | Some info -> info  (* Si déjà défini localement, utiliser l'info existante *)
        | None -> 
          (* Création de l'info pour chaque paramètre et ajout à la TDS fille *)
          let info_param = Tds.InfoVar (n, t, 0, "") in
          let info_ast = info_to_info_ast info_param in
          ajouter tds_fille n info_ast;
          info_ast
      in
      (* Analyse des expressions pour les valeurs par défaut des paramètres *)
      let converted_vop = match vop with
        | Some exp -> Some (analyse_tds_expression tds_fille tdp exp)
        | None -> None
      in
      (t, info_ast, converted_vop)
    ) lp in

    (* Génération de la liste des valeurs par défaut analysées pour chaque paramètre et ajout dans le tableau `tdp` *)
    let lst_tdp = List.map (fun (_, _, vop) -> 
      match vop with
      | Some exp -> Some (analyse_tds_expression tds_fille tdp exp)  (* Analyse des valeurs par défaut *)
      | None -> None
    ) lp in
    Hashtbl.add tdp n lst_tdp;  (* Association du nom de la fonction avec ses paramètres par défaut dans le `tdp` *)

    (* Analyse du bloc d'instructions de la fonction *)
    let nli = analyse_tds_bloc tds_fille tdp (Some info_fun_ast) li in

    (* Retour de la fonction analysée avec les paramètres et le bloc d'instructions convertis *)
    AstTds.Fonction (t, info_fun_ast, nlp_converted, nli)

    let analyse_tds_var tds tdp v = 
      match v with 
      | AstSyntax.DeclarationStatique (t,n,e) -> 
        begin
          match chercherLocalement tds n with
          (* On ne peut déclarer une variable statique qu'une seule fois avant le corps du programme *)
          | None -> 
            let ne = (analyse_tds_expression tds tdp e) in
            let info = InfoVar (n,t,0,"") in
            let info_ast = info_to_info_ast info in
            ajouter tds n info_ast;
            AstTds.DeclarationStatique(t,info_ast,ne)
          | Some _ -> raise (DoubleDeclaration n)
        end
    



(* analyser : AstSyntax.programme -> AstTds.programme *)
(* analyser : AstSyntax.programme -> AstTds.programme *)
let analyser (AstSyntax.Programme (vars,fonctions,prog)) =
  let tds = creerTDSMere () in
  let tdp = Hashtbl.create 32 in
  let nv = List.map (fun v -> analyse_tds_var tds tdp v) vars in
  let nf = List.map (fun f -> analyse_tds_fonction tds tdp f) fonctions in
  let nb = analyse_tds_bloc tds tdp None prog in
  AstTds.Programme (nv,nf,nb)






