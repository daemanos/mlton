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
      val empty : 'a t
      val isEmpty : 'a t -> bool
      val singleton : (Key.ord_key * 'a) -> 'a t
      val insert  : 'a t * Key.ord_key * 'a -> 'a t
      val insert' : ((Key.ord_key * 'a) * 'a t) -> 'a t
      val insertWith  : ('a * 'a -> 'a) -> 'a t * Key.ord_key * 'a -> 'a t
      val insertWithi : (Key.ord_key * 'a * 'a -> 'a) -> 'a t * Key.ord_key * 'a -> 'a t
      val find : 'a t * Key.ord_key -> 'a option
      val lookup : 'a t * Key.ord_key -> 'a
      val inDomain : ('a t * Key.ord_key) -> bool
      val remove : 'a t * Key.ord_key -> 'a t * 'a
      val first : 'a t -> 'a option
      val firsti : 'a t -> (Key.ord_key * 'a) option
      val numItems : 'a t ->  int
      val listItems  : 'a t -> 'a list
      val listItemsi : 'a t -> (Key.ord_key * 'a) list
      val listKeys : 'a t -> Key.ord_key list
      val collate : ('a * 'a -> order) -> ('a t * 'a t) -> order
      val unionWith  : ('a * 'a -> 'a) -> ('a t * 'a t) -> 'a t
      val unionWithi : (Key.ord_key * 'a * 'a -> 'a) -> ('a t * 'a t) -> 'a t
      val intersectWith  : ('a * 'b -> 'c) -> ('a t * 'b t) -> 'c t
      val intersectWithi : (Key.ord_key * 'a * 'b -> 'c) -> ('a t * 'b t) -> 'c t
      val mergeWith : ('a option * 'b option -> 'c option)
            -> ('a t * 'b t) -> 'c t
      val mergeWithi : (Key.ord_key * 'a option * 'b option -> 'c option)
            -> ('a t * 'b t) -> 'c t
      val app  : ('a -> unit) -> 'a t -> unit
      val appi : ((Key.ord_key * 'a) -> unit) -> 'a t -> unit
      val map  : ('a -> 'b) -> 'a t -> 'b t
      val mapi : (Key.ord_key * 'a -> 'b) -> 'a t -> 'b t
      val foldl  : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b
      val foldli : (Key.ord_key * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b
      val foldr  : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b
      val foldri : (Key.ord_key * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b
      val filter  : ('a -> bool) -> 'a t -> 'a t
      val filteri : (Key.ord_key * 'a -> bool) -> 'a t -> 'a t
      val mapPartial  : ('a -> 'b option) -> 'a t -> 'b t
      val mapPartiali : (Key.ord_key * 'a -> 'b option) -> 'a t -> 'b t
      val exists : ('a -> bool) -> 'a t -> bool
      val existsi : (Key.ord_key * 'a -> bool) -> 'a t -> bool
      val all : ('a -> bool) -> 'a t -> bool
      val alli : (Key.ord_key * 'a -> bool) -> 'a t -> bool

      (* added lattice operations *)
      val zip: 'a t * 'b t -> ('a option * 'b option) t
      val join: ('a * 'a -> 'a option) -> 'a t * 'a t -> 'a t option
   end
