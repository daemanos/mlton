(* Copyright (C) 2009 Matthew Fluet.
 * Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature HEAP_STRUCTS =
   sig
      structure Key: ORDER
   end

signature HEAP =
   sig
      include HEAP_STRUCTS

      exception EmptyHeap

      structure Elt:
         sig
            type 'a t

            val key: 'a t -> Key.t
            val value: 'a t -> 'a
         end

      type 'a t

      val deleteMin: 'a t -> 'a * 'a t
      val empty: unit -> 'a t
      val insert: 'a t * Key.t * 'a -> 'a t
      val isEmpty: 'a t -> bool
      val merge: 'a t * 'a t -> 'a t
      val min: 'a t -> 'a
      val new: (Key.t * 'a) list -> 'a t
      val singleton: Key.t * 'a -> 'a t
      val size: 'a t -> int
   end
