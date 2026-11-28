module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.ProjectionQuote.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedTable

/-! # Replay of extensionally equal ordered terminal tables -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance computedTableHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

local notation "Discards" => Paper.Extension.ReturnDiscards Seed

/-- A finite expression and its full quote replay against the same open slots
in the compiler's fixed newest-first order. The quote can test unused slots,
so the slot computations must admit native discard. -/
theorem quote_eval_selected {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (e : Finite.Expr n) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit)
    (bits : List Bool) (drop : ∀ j, Discards [X] (slots j).elaborate.val) :
    selectedEq (selectTerminal pos (Finite.Expr.quote n e.eval) slots bits)
      (selectTerminal pos e slots bits) :=
  ComputedTable.quote_eval_selected e pos slots bits drop

/-- Pointwise agreement of the Boolean rows yields a native equation at the
shared open slot map, emit prefix, and typed position. -/
theorem computed_table_eq {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (e f : Finite.Expr n) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit)
    (bits : List Bool) (drop : ∀ j, Discards [X] (slots j).elaborate.val)
    (rows : ∀ env, e.eval env = f.eval env) :
    selectedEq (selectTerminal pos e slots bits) (selectTerminal pos f slots bits) :=
  ComputedTable.computed_table_eq e f pos slots bits drop rows

/-- Row equality identifies the actual packed selected arrows from the full
retained input product to the shared tagged exit interface. -/
theorem packed_computed_table_eq {L : List (Ty Empty)} {n : Nat}
    (e f : Finite.Expr n) (pos : Position L) (bits : List Bool)
    (rows : ∀ env, e.eval env = f.eval env) :
    packed (.retExpr bits pos e) = packed (.retExpr bits pos f) :=
  ComputedTable.packed_computed_table_eq e f pos bits rows

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
