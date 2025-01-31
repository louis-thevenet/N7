open Ast 
open MiniML

let%test _ = ( (miniML "../../exemples/exemple-00.mml") = (IntegerValue 3))
let%test _ = ( (miniML "../../exemples/exemple-01.mml") = (IntegerValue (-8)))
let%test _ = ( (miniML "../../exemples/exemple-02.mml") = (IntegerValue 4))
let%test _ = ( (miniML "../../exemples/exemple-03.mml") = (IntegerValue 5))
let%test _ = ( (miniML "../../exemples/exemple-04.mml") = (IntegerValue 1))
let%test _ = ( (miniML "../../exemples/exemple-05.mml") = (IntegerValue 2))
let%test _ = ( (miniML "../../exemples/exemple-06.mml") = (IntegerValue 120))
let%test _ = ( (miniML "../../exemples/exemple-07.mml") = (IntegerValue 10))
let%test _ = ( (miniML "../../exemples/exemple-08.mml") = (IntegerValue 5))
let%test _ = ( (miniML "../../exemples/exemple-09.mml") = (FrozenValue (FunctionNode ("x",AccessNode "x"),[])))
let%test _ = ( (miniML "../../exemples/exemple-11.mml") = (IntegerValue 120))
let%test _ = ( (miniML "../../exemples/exemple-12.mml") = (IntegerValue 120))
               
