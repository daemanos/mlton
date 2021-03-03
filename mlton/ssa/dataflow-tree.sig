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

      (* Fact definition *)
      structure FactBase : sig
         type 'a t

         val empty : 'a t
         val fromList: (Label.t * 'a) list -> 'a t

         val insert : 'a t -> (Label.t * 'a) -> 'a t
         val lookup : 'a t -> Label.t -> 'a option
      end

      structure Node : sig
         datatype t = L of Label.t
                    | S of Statement.t
                    | T of Transfer.t
      end

      structure ReplaceNode : sig
         datatype t = Blocks of {entry: Statement.t vector * Transfer.t,
                                 blocks: Block.t vector,
                                 return: Label.t * Statement.t vector}
                    | Statements of Statement.t vector
                    | Transfer of Transfer.t
                    | Empty
      end

      type 'f rw = Node.t -> 'f -> ReplaceNode.t option

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
      type 'f transferLb = Label.t -> 'f -> 'f

      (* propagate facts after a statement within a block *)
      type 'f transferSt = Statement.t -> 'f -> 'f

      (* resolve outgoing facts by target label *)
      type 'f transferTr = Transfer.t -> 'f -> 'f FactBase.t

      (* triple of transfer functions *)
      type 'f transfer = ('f transferLb * 'f transferSt * 'f transferTr)

      (* helper combinator to package transfers *)
      val mkTransfer : 'f transferLb ->
                       'f transferSt ->
                       'f transferTr ->
                       'f transfer

   end
