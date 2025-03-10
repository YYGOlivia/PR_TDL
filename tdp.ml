open Ast
open Hashtbl

(* Définir le type tdp, utilisant Hashtbl *)
type tdp = (string, Ast.AstTds.expression option list) Hashtbl.t

(* Initialiser un tdp vide *)
let init_tdp () : tdp = Hashtbl.create 32

(* Obtenir la liste des valeurs par défaut des paramètres pour un nom de fonction donné, retourne None si elle n'existe pas *)
let get (tdp: tdp) (nom: string) : Ast.AstTds.expression option list option =
  try Some (Hashtbl.find tdp nom)
  with Not_found -> None

(* Ajouter ou mettre à jour le nom de la fonction et sa liste de paramètres par défaut *)
let add (tdp: tdp) (nom: string) (params: Ast.AstTds.expression option list) : unit =
  Hashtbl.replace tdp nom params
