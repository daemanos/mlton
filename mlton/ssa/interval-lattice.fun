functor IntervalLattice (S: INTERVAL_LATTICE_STRUCTS): INTERVAL_LATTICE =
struct

  open S

  structure Bound = struct
    datatype t = Min | Max | Val of IntInf.int

    fun compare (b1, b2) = case (b1, b2) of
          (Min, Min) => EQUAL
        | (Max, Max) => EQUAL
        | (Min, _) => LESS
        | (_, Max) => LESS
        | (Max, _) => GREATER
        | (_, Min) => GREATER
        | (Val x1, Val x2) => IntInf.compare (x1, x2)

    fun b1 < b2 = compare (b1, b2) = LESS
    fun b1 <= b2 = case compare (b1, b2) of
                        LESS => true
                      | EQUAL => true
                      | _ => false

    fun b1 > b2 = compare (b1, b2) = GREATER
    fun b1 >= b2 = case compare (b1, b2) of
                        GREATER => true
                      | EQUAL => true
                      | _ => false

    fun b1 + b2 = case (b1, b2) of
        (Min, b) => b
      | (b, Min) => b
      | (Max, _) => Max
      | (_, Max) => Max
      | (Val x1, Val x2) => Val (IntInf.+ (x1, x2))

    fun b1 - b2 = case (b1, b2) of
        (Min, _) => Min
      | (b, Min) => b
      | (Max, _) => Max
      | (_, Max) => Min
      | (Val x1, Val x2) => Val (IntInf.- (x1, x2))

    fun b1 * b2 = case (b1, b2) of
        (Min, _) => Min
      | (_, Min) => Min
      | (Max, _) => Max
      | (_, Max) => Max
      | (Val x1, Val x2) => Val (IntInf.* (x1, x2))

    fun equals (b1, b2) = case (b1, b2) of
          (Min, Min) => true
        | (Max, Max) => true
        | (Val x1, Val x2) => x1 = x2
        | _ => false

    fun min (b1, b2) = case (b1, b2) of
          (Min, _) => Min
        | (_, Min) => Min
        | (b, Max) => b
        | (Max, b) => b
        | (Val x1, Val x2) => Val (IntInf.min (x1, x2))

    fun minimum bs = List.foldr (bs, Max, min)

    fun max (b1, b2) = case (b1, b2) of
          (Max, _) => Max
        | (_, Max) => Max
        | (b, Min) => b
        | (Min, b) => b
        | (Val x1, Val x2) => Val (IntInf.max (x1, x2))

    fun maximum bs = List.foldr (bs, Min, max)

    fun pred b = case b of
        Val x => Val (IntInf.- (x, 1))
      | b' => b'

    fun toString b = case b of
        Min => "MIN"
      | Max => "MAX"
      | Val x => IntInf.toString x
  end

  structure Interval = struct
    open Bound

    datatype t = Bot | Top | Range of Bound.t * Bound.t

    (* Normalize an interval:
     *  - Convert Range (Min, Max) to the canonical representation, Top
     *  - Maintain the invariant that Range (l, h) ==> l <= h by converting
     *    nonconforming ranges to Bot
     * *)
    fun normalize i = case i of
        Range (Min, Max) => Top
      | Range (l, h) => if l > h
                        then Bot
                        else i
      | _ => i

    fun equals (i1, i2) = case (i1, i2) of
          (Bot, Bot) => true
        | (Top, Top) => true
        | (Range (l1, h1), Range (l2, h2)) => l1 = l2 andalso h1 = h2
        | _ => false

    fun union (i1, i2) = case (i1, i2) of
          (Top, _) => Top
        | (_, Top) => Top
        | (Bot, i) => i
        | (i, Bot) => i
        | (Range (l1, h1), Range (l2, h2)) => normalize (Range (min (l1, l2),
                                                                max (h1, h2)))

    fun intersect (i1, i2) = case (i1, i2) of
          (Bot, _) => Bot
        | (_, Bot) => Bot
        | (Top, i) => i
        | (i, Top) => i
        | (Range (l1, h1), Range (l2, h2)) => normalize (Range (max (l1, l2),
                                                                min (h1, h2)))

    fun i1 < i2 = equals (i2, union (i1, i2))

    fun apply f (i1, i2) = case (i1, i2) of
        (Bot, _) => Bot
      | (_, Bot) => Bot
      | (Top, _) => Top
      | (_, Top) => Top
      | (Range (l1, h1), Range (l2, h2)) => normalize (Range (f (l1, l2),
                                                              f (h1, h2)))

    fun i1 + i2 = apply Bound.+ (i1, i2)
    fun i1 - i2 = apply Bound.- (i1, i2)
    fun i1 * i2 = apply Bound.* (i1, i2)

    (*
     * Basic widening function: uses B, the list of all integer constants in
     * the program, to widen interval I.
     *)
    fun widen b i = case i of
        Bot => Bot
      | Top => Top
      | Range (l,h) =>
          let
            val l' = maximum (List.foldr (b, [], (fn (x,xs) => if l >= x
                                                               then (x::xs)
                                                               else xs)))
            val h' = minimum (List.foldr (b, [], (fn (x,xs) => if h <= x
                                                              then (x::xs)
                                                              else xs)))
          in
            Range (l', h')
          end

    fun refineRight (i1, i2) = case (i1, i2) of
        (Bot, _) => Bot
      | (_, Bot) => Bot
      | (Top, Range (_, h)) => Range (Min, pred h)
      | (_, Top) => i1
      | (Range (l, _), Range (_, h)) => intersect (i1, Range (l, pred h))

    fun refineLeft (i1, i2) = case (i1, i2) of
        (Bot, _) => Bot
      | (_, Bot) => Bot
      | (Top, Range (l, _)) => Range (l, Max)
      | (Range (_, h), Range (l, _)) => intersect (i1, Range (l, h))

    fun toString i = case i of
        Top => "TOP"
      | Bot => "BOT"
      | Range (l, h) => "<" ^ Bound.toString l ^ ", " ^ Bound.toString h ^ ">"
  end

  open Interval

  datatype t = T of {value: Interval.t ref,
                     size: WordSize.t option}

  fun new w: t = T {value = ref Bot, size = w}

  fun value (T {value, ...}) = !value
  fun size (T {size, ...}) = size
  fun setValue (T {value, ...}, value') = value := value'

end
