(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor DataflowTransform(
   structure P: DATAFLOW_PROBLEM
   structure S: SSA_TRANSFORM_STRUCTS): SSA_TRANSFORM =
struct

open P
open S

(* Optimization fuel *)
val fuel: int ref = ref 0

(* Rolling back speculative rewrites *)
(* TODO real implementation *)
fun checkpoint () = ()
fun restart () = ()


(* TODO real implementation *)
fun transform p =
let
   (* suppress unused warnings *)
   val _ = !fuel
   val _ = checkpoint ()
   val _ = restart ()
in
   p
end

end
