(*open Semantics*)
open MiniML
open Types

let getValeur (_, v, _) = v
let getType (t, _, _) = t

(* Tests de non regression *)
let%test _ = getValeur (miniML "../../exemples/exemple-00.mml") = IntegerValue 3
let%test _ = getType (miniML "../../exemples/exemple-00.mml") = IntegerType

let%test _ =
  getValeur (miniML "../../exemples/exemple-01.mml") = IntegerValue (-8)

let%test _ = getValeur (miniML "../../exemples/exemple-02.mml") = IntegerValue 4
let%test _ = getValeur (miniML "../../exemples/exemple-03.mml") = IntegerValue 5
let%test _ = getValeur (miniML "../../exemples/exemple-04.mml") = IntegerValue 1
let%test _ = getValeur (miniML "../../exemples/exemple-05.mml") = IntegerValue 2

let%test _ =
  getValeur (miniML "../../exemples/exemple-06.mml") = IntegerValue 120

let%test _ =
  getValeur (miniML "../../exemples/exemple-07.mml") = IntegerValue 10

let%test _ = getValeur (miniML "../../exemples/exemple-08.mml") = IntegerValue 5

let%test _ =
  getValeur (miniML "../../exemples/exemple-09.mml")
  = FrozenValue (FunctionNode ("x", AccessNode "x"), [])

let%test _ =
  getValeur (miniML "../../exemples/exemple-11.mml") = IntegerValue 120

let%test _ =
  getValeur (miniML "../../exemples/exemple-12.mml") = IntegerValue 120

let%test _ =
  getValeur (miniML "../../exemples/exemple-13.mml") = IntegerValue 11

let%test _ = getValeur (miniML "../../exemples/exemple-14.mml") = IntegerValue 1

let%test _ =
  getValeur (miniML "../../exemples/exemple-15.mml") = IntegerValue 63

let%test _ = getType (miniML "../../exemples/exemple-00.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-01.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-02.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-03.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-04.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-05.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-06.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-07.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-08.mml") = IntegerType

(* let _ = *)
(* print_string *)
(* (string_of_type (getType (miniML "../../exemples/exemple-09.mml"))) *)

(*Je comprends pas pourquoi il échoue, le type renvoyé est bien (('1 unknown) -> ('1 unknown)) *)
let%test _ =
  getType (miniML "../../exemples/exemple-09.mml")
  = FunctionType (UnknownType, UnknownType)

let%test _ = getType (miniML "../../exemples/exemple-11.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-12.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-13.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-14.mml") = IntegerType
let%test _ = getType (miniML "../../exemples/exemple-15.mml") = IntegerType
