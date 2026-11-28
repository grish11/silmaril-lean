module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.ProjectionQuote.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms

/-! # Replay of extensionally equal ordered terminal tables -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedTable

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open CaseTree.ReplyAgreement.NativeReplay (case_congr)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper.WithCaseBind.OpenReplay

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

local notation "Discards" => Paper.Extension.ReturnDiscards Seed

private theorem quote_split {n : Nat} (low high : Finite.Expr n) :
    Finite.Expr.quote (n + 1) (Finite.Expr.split low high).eval =
      .split (Finite.Expr.quote n low.eval) (Finite.Expr.quote n high.eval) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem quote_eval_selected {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (e : Finite.Expr n) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit)
    (bits : List Bool) (drop : ∀ j, Discards [X] (slots j).elaborate.val) :
    selectedEq (selectTerminal pos (Finite.Expr.quote n e.eval) slots bits)
      (selectTerminal pos e slots bits) := by
  induction e generalizing X bits with
  | literal b => exact constant_quote b pos slots bits drop
  | read i => exact projection_quote i pos slots bits (fun j _ => drop j)
  | split low high il ir =>
    let older (j : Fin _) := retainSlot (A := unit) (slots j.succ)
    have olderDrop (j : Fin _) : Discards [product X unit] (older j).elaborate.val :=
      retainSlot_discards _ (drop j.succ)
    rw [quote_split]
    exact case_congr (emitPrefix bits (slots 0)) (il older [] olderDrop) (ir older [] olderDrop)

theorem computed_table_eq {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (e f : Finite.Expr n) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit)
    (bits : List Bool) (drop : ∀ j, Discards [X] (slots j).elaborate.val)
    (rows : ∀ env, e.eval env = f.eval env) :
    selectedEq (selectTerminal pos e slots bits) (selectTerminal pos f slots bits) := by
  have sameTable := funext rows
  exact (quote_eval_selected e pos slots bits drop).symm.trans
    (sameTable.symm ▸ quote_eval_selected f pos slots bits drop)

theorem packed_computed_table_eq {L : List (Ty Empty)} {n : Nat}
    (e f : Finite.Expr n) (pos : Position L) (bits : List Bool)
    (rows : ∀ env, e.eval env = f.eval env) :
    packed (.retExpr bits pos e) = packed (.retExpr bits pos f) :=
  packed_congr (computed_table_eq e f pos (readReply n) bits (readReply_discards n) rows)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedTable
