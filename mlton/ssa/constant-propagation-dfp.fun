(* Copyright (C) 2017,2019-2020 Matthew Fluet.
 * Copyright (C) 1999-2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

(* NOTE: copying copyright holders since I plan to base this on the original
 * implementation *)

functor ConstantPropagationDFP(S: SSA_TRANSFORM_STRUCTS): DATAFLOW_PROBLEM =
struct

open S

(* FIXME dummy implementation *)

type f = unit
type change = unit option

structure FactBase =
struct
   type 'a t = (Label.t * 'a) list

   fun mkLabelMap las = las

   fun insert las la = la::las

   fun lookup las l =
      case las of
         ((l',a)::rest) =>
            if Label.equals (l,l') then SOME a
            else lookup rest l
       | [] => NONE
end

datatype 'a Fact = Open of 'a
                 | Closed of 'a FactBase.t

val bot = ()
fun join _ _ = (NONE, ())

fun transfer _ _ = Open () 

fun rewrite _ _ = NONE

end
