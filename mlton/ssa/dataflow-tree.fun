(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor DataflowTree(S: SSA_TRANSFORM_STRUCTS): DATAFLOW_TREE =
struct

open S

val {get = labelArgs: Label.t -> (Var.t * Type.t) vector,
     set = setLabelArgs, ...} =
   Property.getSet
   (Label.plist, Property.initRaise ("labelArgs", Label.layout))
val {get = conType, set = setConType, ...} =
   Property.getSetOnce
   (Con.plist, Property.initRaise ("conType", Con.layout))

(* helper constructor for lattice types *)
(* TODO probably put somewhere more relevant *)
datatype 'f Poset = Top
                  | Elt of 'f
                  | Bot

fun layoutPoset layoutF poset =
   let
      open Layout
   in
      case poset of
         Top => str "Top"
       | Bot => str "Bot"
       | Elt f => seq [str "Elt[", layoutF f, str "]"]
   end

fun joinPoset joinElt =
   fn (old, new) =>
      case (old, new) of
         (_, Bot) => NONE
       | (Bot, _) => SOME new
       | (Top, _) => NONE
       | (_, Top) => SOME Top
       | (Elt old, Elt new) => joinElt (old, new)

structure VarMapLattice =
struct
   structure Lattice = MapLattice (struct
      type ord_key = Var.t
      fun compare (u, v) = Word.compare (Var.hash u, Var.hash v)
   end)

   open Lattice
   fun layout layoutElt m = layout'' (m, Var.layout, layoutElt)
end

structure FactBase =
struct
   structure M = RedBlackMapFn (struct
      type ord_key = Label.t
      fun compare (l, l') = Word.compare (Label.hash l, Label.hash l')
   end)

   type 'a t = 'a M.map
   exception NotFound

   val empty = M.empty
   val singleton = M.singleton
   val map = M.map
   val foldi = M.foldli
   val fold = M.foldl
   val insert = M.insert
   val insertWith = M.insertWith

   fun uniform (ls, a) =
      List.fold (ls, empty, fn (l, fbase) => insert (fbase, l, a))

   fun insertWithJoin join =
      insertWith (fn (old, new) => getOpt (join (old, new), old))

   fun fromCases (cases, default, fact, do_con) =
   let
      val default_la =
         case default of
            SOME label => singleton (label, fact)
          | _ => empty
   in
      case cases of
         Cases.Con conLabels =>
            Vector.fold
            (conLabels,
             default_la,
             fn ((con, label), acc) =>
                case do_con (con, label) of
                   SOME fact' => insert (acc, label, fact')
                 | _ => insert (acc, label, fact))
       | Cases.Word (_, wordLabels) =>
            Vector.fold
            (wordLabels,
             default_la,
             fn ((_, label), acc) => insert (acc, label, fact))
   end

   (* TODO should probably make this line up more with M *)

   fun lookup (las, l) = SOME (M.lookup (las, l)) handle _ => NONE
   val isMember = M.inDomain

   fun deleteList ls las =
      List.fold
      (ls, las, fn (label, fbase) => #1 (M.remove (fbase, label)))

   fun layout layoutA las =
      let open Layout
      in
         record
         (foldi
          (fn (label, a, layouts) =>
           (Label.toString label, layoutA a) :: layouts)
          [] las)
      end
end

type prefix = {args: (Var.t * Type.t) vector,
               label: Label.t,
               statements: Statement.t vector}

type suffix = {statements: Statement.t vector,
               transfer: Transfer.t}

type 'f rwLb = (Var.t * Type.t) vector * Label.t -> 'f ->
               {blocks: Block.t list, prefix: prefix} option

fun norwLb _ _ = NONE

type 'f rwTr = Transfer.t -> 'f ->
               {suffix: suffix, blocks: Block.t list} option

fun replaceTr tr =
   SOME {suffix = {statements = Vector.new0 (),
                   transfer = tr},
         blocks = []}

fun norwTr _ _ = NONE

datatype ReplaceSt = Statements of Statement.t vector
                   | Graph of {suffix: suffix,
                               blocks: Block.t list,
                               prefix: prefix}

type 'f rwSt = Statement.t -> 'f -> ReplaceSt option

fun replaceSt1 st = SOME (Statements (Vector.new1 st))

fun norwSt _ _ = NONE

type 'f rw = ('f rwLb * 'f rwSt * 'f rwTr)

(* helper function to package rewrite functions *)
fun mkRw rwLb rwSt rwTr = (rwLb, rwSt, rwTr)

datatype 'f rewrite = Doit of 'f rw
                    | Then of ('f rewrite * 'f rewrite)
                    | Iter of 'f rewrite
                    | Noop

fun mkRewrite r = Doit r
fun thenRewrite r1 r2 = Then (r1, r2)
fun iterRewrite r = Iter r
fun deepRewrite r = Iter (Doit r)

type 'f transferLb = (Var.t * Type.t) vector * Label.t -> 'f -> 'f
type 'f transferSt = Statement.t -> 'f -> 'f
type 'f transferTr = Transfer.t -> 'f -> 'f FactBase.t

type 'f transfer = ('f transferLb * 'f transferSt * 'f transferTr)

fun mkTransfer lb st tr = (lb, st, tr)

end
