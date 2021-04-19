(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature DATAFLOW_TREE_STRUCTS =
   sig
      include RESTORE
   end

signature DATAFLOW_TREE =
   sig
      include DATAFLOW_TREE_STRUCTS

      (* Properties of the program; will be initialized by DataflowTransform
       * before any analysis is performed *)
      val labelArgs : Label.t -> (Var.t * Type.t) vector
      val setLabelArgs : Label.t * (Var.t * Type.t) vector -> unit

      (* helper constructor for lattice types *)
      (* TODO probably put somewhere more relevant *)
      datatype 'f Poset = Top
                        | Elt of 'f
                        | Bot

      val layoutPoset : ('f -> Layout.t) -> 'f Poset -> Layout.t

      (* predefined map lattice for variables *)
      structure VarMapLattice: sig
         include MAP_LATTICE
         val layout' : 'a t * ('a -> Layout.t) -> Layout.t
      end

      (* Fact definition *)
      structure FactBase : sig
         type 'a t

         val empty : 'a t
         val singleton: Label.t * 'a -> 'a t
         val fromList: (Label.t * 'a) list -> 'a t
         val uniform: Label.t list * 'a -> 'a t

         val fromCases: (Con.t, Label.t) Cases.t * Label.t option * 'a *
                        (Con.t * Label.t -> 'a option) -> 'a t

         val insert : 'a t -> (Label.t * 'a) -> 'a t
         val lookup : 'a t -> Label.t -> 'a option
         val isMember : 'a t -> Label.t -> bool
         val deleteList : Label.t list -> 'a t -> 'a t

         val foldi : (Label.t * 'a -> 'b -> 'b) -> 'b -> 'a t -> 'b
         val fold : ('a -> 'b -> 'b) -> 'b -> 'a t -> 'b

         val layout' : 'a t * ('a -> Layout.t) -> Layout.t
      end

      (* block prefix : arguments to the block, a label, and 0 or more
       * statements *)
      type prefix = {args: (Var.t * Type.t) vector,
                     label: Label.t,
                     statements: Statement.t vector}

      (* block suffix : 0 or more statements followed by a transfer *)
      type suffix = {statements: Statement.t vector,
                     transfer: Transfer.t}

      (* A closed/open node is an (args, label) pair and a closed/open graph
       * is a sequence of 0 or more blocks followed by a replacement closed/open
       * node and a sequence of 0 or more statements *)
      type 'f rwLb = (Var.t * Type.t) vector * Label.t -> 'f ->
                     {blocks: Block.t list, prefix: prefix} option

      val norwLb : 'f rwLb

      (* An open/closed node is a transfer and an open/closed graph is a
       * sequence of 0 or more statements followed by a transfer and 0 or more
       * additional blocks *)
      type 'f rwTr = Transfer.t -> 'f ->
                     {suffix: suffix, blocks: Block.t list} option

      val replaceTr : Transfer.t -> {suffix: suffix, blocks: Block.t list} option

      val norwTr : 'f rwTr

      datatype ReplaceSt = Statements of Statement.t vector
                         | Graph of {suffix: suffix,
                                     blocks: Block.t list,
                                     prefix: prefix}

      (* An open/open node is a statement and an open/open graph is either a
       * sequence of 0 or more statements or a new block suffix followed by any
       * number of additional blocks and a new block prefix *)
      type 'f rwSt = Statement.t -> 'f -> ReplaceSt option

      val replaceSt1 : Statement.t -> ReplaceSt option

      val norwSt : 'f rwSt

      type 'f rw = ('f rwLb * 'f rwSt * 'f rwTr)

      (* helper function to package rewrite functions *)
      val mkRw : 'f rwLb -> 'f rwSt -> 'f rwTr -> 'f rw

      datatype 'f rewrite = Doit of 'f rw
                          | Then of ('f rewrite * 'f rewrite)
                          | Iter of 'f rewrite
                          | Noop

      (* helper combinators to package rewrites *)
      val mkRewrite : 'f rw -> 'f rewrite
      val thenRewrite : 'f rewrite -> 'f rewrite -> 'f rewrite
      val iterRewrite : 'f rewrite -> 'f rewrite
      val deepRewrite : 'f rw -> 'f rewrite

      (* introduce incoming facts to a new block *)
      type 'f transferLb = (Var.t * Type.t) vector * Label.t -> 'f -> 'f

      (* propagate facts after a statement within a block *)
      type 'f transferSt = Statement.t -> 'f -> 'f

      (* resolve outgoing facts by target label *)
      type 'f transferTr = Transfer.t -> 'f -> 'f FactBase.t

      (* triple of transfer functions *)
      type 'f transfer = ('f transferLb * 'f transferSt * 'f transferTr)

      (* helper function to package transfers *)
      val mkTransfer : 'f transferLb ->
                       'f transferSt ->
                       'f transferTr ->
                       'f transfer

   end
