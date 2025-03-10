type typ = Bool | Int | Rat | Pointeur of typ | Undefined 

let rec string_of_type t = 
  match t with
  | Bool ->  "Bool"
  | Int  ->  "Int"
  | Rat  ->  "Rat"
  | Pointeur t -> "Pointeur "^string_of_type t
  | Undefined -> "Undefined"


let rec est_compatible t1 t2 =
  match t1, t2 with
  | Bool, Bool -> true
  | Int, Int -> true
  | Rat, Rat -> true 
  (* Un pointeur ne peut être compatible qu'avec un pointeur *)
  | Pointeur a, Pointeur b -> 
    (* Mais ne l'est pas nécessairement donc on vérifie les types associés aux pointeurs. *)
    begin
      match a, b with 
      (* Si l'un des deux est indéfini alors ils sont nécessairement compatibles. *)
      | Undefined, _ -> true
      | _, Undefined -> true
      (* Sinon, la compatibilité est déterminée par la récursion sur les types pointés (a et b) *) 
      | _,_ -> (est_compatible a b)
    end
  | _ -> false 

let%test _ = est_compatible Bool Bool
let%test _ = est_compatible Int Int
let%test _ = est_compatible Rat Rat
let%test _ = not (est_compatible Int Bool)
let%test _ = not (est_compatible Bool Int)
let%test _ = not (est_compatible Int Rat)
let%test _ = not (est_compatible Rat Int)
let%test _ = not (est_compatible Bool Rat)
let%test _ = not (est_compatible Rat Bool)
let%test _ = not (est_compatible Undefined Int)
let%test _ = not (est_compatible Int Undefined)
let%test _ = not (est_compatible Rat Undefined)
let%test _ = not (est_compatible Bool Undefined)
let%test _ = not (est_compatible Undefined Int)
let%test _ = not (est_compatible Undefined Rat)
let%test _ = not (est_compatible Undefined Bool)

(* On ajoute les tests pour l'ajout des pointeurs *)
let%test _ = est_compatible (Pointeur Int) (Pointeur Int)
let%test _ = est_compatible (Pointeur Bool) (Pointeur Bool)
let%test _ = est_compatible (Pointeur Rat) (Pointeur Rat)
let%test _ = not (est_compatible (Pointeur Int) (Pointeur Bool))
let%test _ = not (est_compatible (Pointeur Bool) (Pointeur Int))
let%test _ = not (est_compatible (Pointeur Int) (Pointeur Rat))
let%test _ = not (est_compatible (Pointeur Rat) (Pointeur Int))
let%test _ = not (est_compatible (Pointeur Bool) (Pointeur Rat))
let%test _ = not (est_compatible (Pointeur Rat) (Pointeur Bool))
let%test _ = est_compatible (Pointeur Undefined) (Pointeur Int)
let%test _ = est_compatible (Pointeur Int) (Pointeur Undefined)
let%test _ = est_compatible (Pointeur Undefined) (Pointeur Bool)
let%test _ = est_compatible (Pointeur Bool) (Pointeur Undefined)
let%test _ = est_compatible (Pointeur Undefined) (Pointeur Rat)
let%test _ = est_compatible (Pointeur Rat) (Pointeur Undefined)

let est_compatible_list lt1 lt2 =
  try
    List.for_all2 est_compatible lt1 lt2
  with Invalid_argument _ -> false

let%test _ = est_compatible_list [] []
let%test _ = est_compatible_list [Int ; Rat] [Int ; Rat]
let%test _ = est_compatible_list [Bool ; Rat ; Bool] [Bool ; Rat ; Bool]
let%test _ = not (est_compatible_list [Int] [Int ; Rat])
let%test _ = not (est_compatible_list [Int] [Rat ; Int])
let%test _ = not (est_compatible_list [Int ; Rat] [Rat ; Int])
let%test _ = not (est_compatible_list [Bool ; Rat ; Bool] [Bool ; Rat ; Bool ; Int])

(* Ajout de quelques tests pour les pointeurs mais non exhaustifs car c'est la fonction est_compatible qui est appliquée de manière très simple *)
let%test _ = est_compatible_list [Pointeur Bool; Pointeur Rat; Pointeur Bool] [Pointeur Bool; Pointeur Rat; Pointeur Bool]
let%test _ = not (est_compatible_list [Pointeur Bool; Pointeur Rat; Pointeur Bool] [Pointeur Bool; Pointeur Rat; Pointeur Bool; Pointeur Int])


let rec getTaille t =
  match t with
  | Int -> 1
  | Bool -> 1
  | Rat -> 2
  | Pointeur t -> getTaille t
  | Undefined -> 0
  
let%test _ = getTaille Int = 1
let%test _ = getTaille Bool = 1
let%test _ = getTaille Rat = 2
(* Test pour les pointeurs *)
let%test _ = getTaille (Pointeur Int) = 1
let%test _ = getTaille (Pointeur Bool) = 1
let%test _ = getTaille (Pointeur Rat) = 2


let rec getTailleListe l =
  match l with
  | [] -> 0
  | t::q -> (getTaille t) + getTailleListe q

  let%test _ = getTailleListe [Int;Int;Int] = 3
  let%test _ = getTailleListe [Int;Int;Int;Bool;Rat] = 6
  let%test _ = getTailleListe [Int;Rat;Int;Bool;Rat] = 7
  (* Test pour les pointeurs *)
  let%test _ = getTailleListe [Pointeur Int; Pointeur Int; Pointeur Int] = 3
  let%test _ = getTailleListe [Pointeur Int; Pointeur Int; Pointeur Int; Pointeur Bool; Pointeur Rat] = 6

