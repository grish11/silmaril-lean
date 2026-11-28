module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryDecisionReadback

/-! # Exact replay of staged pure query decisions -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

theorem readDecision_eq {n : Nat} {raw : Region signature.Instr} {d : Decision n}
    (h : readDecision n raw = some d) : raw = d.region :=
  BitQueryDecisionReadback.readDecision_eq h

/-- Invert the chosen leaf at the original scope. The typed unit-binder
substitution discharges the weakening before the continuations are reused. -/
theorem Decision.branches_typed {n : Nat} {Γ L : List (Ty Empty)} (d : Decision n)
    (slots : ∀ i : Fin n, At Γ i.val Bit) (hr : ValueBranches Γ d.region L) :
    ValueBranches (Bit :: Γ) d.left L ∧ ValueBranches (Bit :: Γ) d.right L :=
  BitQueryDecisionReadback.branches_typed d slots hr

theorem Decision.replay {n : Nat} {Γ L : List (Ty Empty)} (d : Decision n)
    (slots : ∀ i : Fin n, At Γ i.val Bit) {l r : Region signature.Instr} (ρ : Nat → Nat)
    (hl : Paper.Eqv (Bit :: Γ) d.left (l.renameLabels ρ) L)
    (hr : Paper.Eqv (Bit :: Γ) d.right (r.renameLabels ρ) L) :
    Paper.Eqv Γ d.region ((⟨d.label, d.query, l, r⟩ : Decision n).region.renameLabels ρ) L :=
  BitQueryDecisionReadback.replay d slots ρ hl hr

/-- Once the single focused operand-beta step is supplied, native case
expansion and binder substitution move this term-level spelling to a staged
decision. The hypothesis is local to the opcode's query. -/
theorem term_case_operand_of (beta : CaseOperandBeta) {Γ L : List (Ty Empty)} {i : Nat}
    (hi : At Γ i Bit) (label : Bool) {l r : Region signature.Instr}
    (hl : ValueBranches (Bit :: Γ) l L) (hr : ValueBranches (Bit :: Γ) r L) :
    Paper.Eqv Γ (.case (.op (.ask label) (caseOperand (.var i))) l r)
      (.case (.var i) ((requestRegion label false l r).renameVars Nat.succ)
        ((requestRegion label true l r).renameVars Nat.succ)) L :=
  BitQueryDecisionReadback.term_case_operand_of beta hi label hl hr

/-- The same focused replay applies in a contextual extension containing
the operand-beta comparison. -/
theorem term_case_operand_extension_of
    {Seed : VCtx (Ty Empty) → Region signature.Instr → Region signature.Instr → LCtx (Ty Empty) → Prop}
    (beta : CaseOperandBetaIn (Paper.Extension.Eqv Seed)) {Γ L : List (Ty Empty)} {i : Nat}
    (hi : At Γ i Bit) (label : Bool) {l r : Region signature.Instr}
    (hl : ValueBranches (Bit :: Γ) l L) (hr : ValueBranches (Bit :: Γ) r L) :
    Paper.Extension.Eqv Seed Γ (.case (.op (.ask label) (caseOperand (.var i))) l r)
      (.case (.var i) ((requestRegion label false l r).renameVars Nat.succ)
        ((requestRegion label true l r).renameVars Nat.succ)) L :=
  BitQueryDecisionReadback.term_case_operand_extension_of beta hi label hl hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback
