functor Heap (S: HEAP_STRUCTS): HEAP =
struct

open S

exception EmptyHeap

structure Elt =
struct
   datatype 'a t = T of {key: Key.t, value: 'a}

   fun new (key, value) = T {key = key, value = value}

   fun op < (T {key = key1, ...}, T {key = key2, ...}) = Key.< (key1, key2)

   fun key (T {key, ...}) = key
   fun value (T {value, ...}) = value
end

datatype 'a t = NonEmpty of {root: 'a Elt.t,
                             left: 'a t,
                             right: 'a t,
                             size: int}
              | Empty

fun min heap =
   case heap of
        NonEmpty {root, ...} => Elt.value root
      | Empty => raise EmptyHeap

fun isEmpty heap =
   case heap of
        NonEmpty _ => false
      | Empty      => true

fun empty () = Empty

fun singleton (key, value)
   = NonEmpty {root = Elt.new (key, value),
               left = Empty,
               right = Empty,
               size = 1}

fun size heap =
   case heap of
        NonEmpty {size, ...} => size
      | Empty => 0

fun merge (heap1, heap2) =
   case (heap1, heap2) of
        (_, Empty) => heap1
      | (Empty, _) => heap2
      | (NonEmpty {root = root1, left = left1, right = right1, ...},
         NonEmpty {root = root2, left = left2, right = right2, ...}) =>
         let
            val (root', st1, st2, st3) =
               if Elt.< (root1, root2)
               then (root1, left1, right1, heap2)
               else (root2, left2, right2, heap1)

            val new = fn (left', right') =>
               NonEmpty {root = root',
                         left = left',
                         right = right',
                         size = size left' + size right'}
         in
            case (st1, st2) of
                 (Empty, _) => new (st2, st3)
               | (_, Empty) => new (st1, st3)
               | _ =>
                  let
                     val sst1 = size st1
                     val sst2 = size st2
                     val sst3 = size st3
                     val (left', right') =
                        if sst1 > sst2
                        then if sst1 > sst3
                             then (st1, merge (st2, st3))
                             else (st3, merge (st1, st2))
                        else if sst2 > sst3
                             then (st2, merge (st1, st3))
                             else (st3, merge (st2, st1))
                  in
                     new (left', right')
                  end
         end

fun deleteMin heap =
   case heap of
        NonEmpty {root, left, right, ...} => (Elt.value root,
                                              merge (left, right))
      | Empty => raise EmptyHeap

fun insert (heap, key, value) = merge (singleton (key, value), heap)

fun new kvs = foldr merge Empty (map singleton kvs)

end
