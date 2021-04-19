(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor MapLattice (K: ORD_KEY) :> MAP_LATTICE where type Key.ord_key = K.ord_key =
struct

structure Map = RedBlackMapFn (K)
open Map

type 'a t = 'a map

fun 'a zip (m1: 'a t, m2: 'b t) : ('a option * 'b option) t
   = mergeWith SOME (m1, m2)

fun 'a join (f: 'a * 'a -> 'a option) (old: 'a t, new: 'a t) : 'a t option =
let
   val changed = ref false
   val zipped = zip (old, new)

   fun joinOne (oldValOpt, newValOpt) =
      case (oldValOpt, newValOpt) of
         (SOME oldVal, SOME newVal) =>
            (case f (oldVal, newVal) of
                SOME val' => (changed := true; val')
              | NONE => newVal)
       | (SOME oldVal, NONE) => oldVal
       | (NONE, SOME newVal) => (changed := true; newVal)
       | _ => raise Fail "MapLattice.join" (* can't happen *)

   val new' = map joinOne zipped
in
   if !changed
   then SOME new'
   else NONE
end

fun 'a layout'' (m: 'a t, layoutKey: Key.ord_key -> Layout.t,
                layoutElt: 'a -> Layout.t): Layout.t =
   let
      open Layout
      val pairs =
         List.map (listItemsi m, fn (key, elt) =>
                   seq [layoutKey key, str ": ", layoutElt elt])
   in
      mayAlign (separate (pairs, ", "))
   end
end
