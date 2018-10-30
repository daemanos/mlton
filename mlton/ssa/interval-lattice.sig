signature INTERVAL_LATTICE_STRUCTS =
sig
  include SHRINK
end

signature INTERVAL_LATTICE =
sig
  include INTERVAL_LATTICE_STRUCTS

  type t

  structure Bound:
  sig
    type t

    val compare: t * t -> order
    val equals: t * t -> bool
    val min: t * t -> t
    val minimum: t list -> t
    val max: t * t -> t
    val maximum: t list -> t
    val pred: t -> t

    val toString: t -> string
  end

  structure Interval:
  sig
    type t

    val equals: t * t -> bool
    val union: t * t -> t
    val intersect: t * t -> t
    val apply: (Bound.t * Bound.t -> Bound.t) -> (t * t) -> t
    val widen: Bound.t list -> t -> t

    val refineRight: t * t -> t
    val refineLeft: t * t -> t

    val toString: t -> string
  end

  val new: WordSize.t option -> t
  val value: t -> Interval.t
  val size: t -> WordSize.t option
  val setValue: t * Interval.t -> unit

end
