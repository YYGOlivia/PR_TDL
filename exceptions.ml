open Type
open Ast.AstSyntax

(* Exceptions pour la gestion des identificateurs *)
exception DoubleDeclaration of string 
exception IdentifiantNonDeclare of string 
exception UndefinedFunction of string
exception MauvaiseUtilisationIdentifiant of string 
exception DerefTargetMustBePointer

(* exception Pas de fonction of string *)
exception IdentIsConstant of string
exception CannotDerefferenceConst
exception DefaultValueNotAtListEnd

(* Exception ajoutée : le nombre d'arguments ne correspond pas *)
exception NombreParametresIncorrect of string * int * int

(* Exceptions pour le typage *)
(* Le premier type est le type réel, le second est le type attendu *)
exception TypeInattendu of typ * typ
exception TypesParametresInattendus of typ list * typ list
exception TypeBinaireInattendu of binaire * typ * typ (* les types sont les types réels non compatible avec les signatures connues de l'opérateur *)

(* Utilisation illégale de return dans le programme principal *)
exception RetourDansMain

(* fonctions d'outils pour aider les constructeurs d'exceptions *)
let raise_nombre_parametres_incorrect nom_func actual expected =
  raise (NombreParametresIncorrect (nom_func, actual, expected))