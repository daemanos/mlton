(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature MAP_LATTICE =
   sig
      structure Key: ORD_KEY

      type 'a t

      (* included from SML/NJ ORD_MAP *)
      val empty: 'a t
      val singleton: (Key.ord_key * 'a) -> 'a t
      val insert: 'a t * Key.ord_key * 'a -> 'a t
      val find: 'a t * Key.ord_key -> 'a option

      (* added lattice operations *)
      val zip: 'a t * 'b t -> ('a option * 'b option) t
      val join: ('a * 'a -> 'a option) -> 'a t * 'a t -> 'a t option
   end
