module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.WithCaseOperandBeta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Obstruction.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Thms

/-! # Replay the existing focused checker in the opt-in quotient -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryCaseOperandReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.RequestTree
open Paper.WithCaseBind.BitQuery.RequestTree.Readback (Candidate CaseOperandBetaIn term_case_operand_extension_of)
open Paper.WithCaseBind.BitQuery.RequestTree.Readback.WithCaseOperandBeta
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

theorem operand_beta : CaseOperandBetaIn Eqv := by
  intro _ _ label b _ _ hl hr
  exact .extra (source_typed label b (.var (i := 0) rfl) hl hr).hasType
    (target_typed label b hl hr).hasType (.reduce label b hl hr)

private theorem left_typed (Γ : List (Ty Empty)) :
    ValueBranches (Bit :: Γ) (.br 0 (.var 0) : Region signature.Instr) Exits :=
  .br (ℓ := 0) rfl (.var (i := 0) rfl)

private theorem right_typed (Γ : List (Ty Empty)) :
    ValueBranches (Bit :: Γ) (.br 1 (.var 0) : Region signature.Instr) Exits :=
  .br (ℓ := 1) rfl (.var (i := 0) rfl)

private theorem original_eq_staged (label : Bool) : packed (original label) = packed (staged label) := by
  have h : Eqv [Bit] (original label).val (staged label).val Exits :=
    term_case_operand_extension_of operand_beta (i := 0) rfl label (left_typed [Bit]) (right_typed [Bit])
  apply (Paper.Extension.Singleton.ofRegion_eq_iff Step _ _).mpr
  exact h.lsubstPost (original label).property (staged label).property
    (fun _ _ hi => (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hi).hasType)

private theorem recognized_exact {r : Region signature.Instr} {label : Bool}
    (h : recognizedLabel r = some label) : r = (original label).val := by
  fun_cases recognizedLabel r
  · simp only [recognizedLabel, Option.some.injEq] at h
    subst label
    rfl
  · rename_i impossible
    unfold recognizedLabel at h
    split at h
    · exact False.elim (impossible _ rfl)
    · cases h

theorem read_packed_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : readTermCase fuel p = some t) : packed p = packedTree t := by
  obtain ⟨label, hlabel, read⟩ := Option.bind_eq_some_iff.mp h
  have source : p = original label := Subtype.ext (recognized_exact hlabel)
  rw [source, original_eq_staged]
  exact congrArg (fun f => (Paper.Extension.Singleton.projection Step).map f)
    (Readback.Candidate.packed_eq_with_decisions read)

theorem original_packed_eq_quote (label : Bool) : packed (original label) = packedTree (quote label) := by
  rw [original_eq_staged]
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Step _ _).mpr
    (.paper (.cfgEta (.native (native_packed_unguarded (quote label)).symm)))

theorem closed_packed_eq (label b : Bool) :
    (Paper.Extension.Singleton.projection Step).map (Readback.Obstruction.sourcePacked label b) =
      (Paper.Extension.Singleton.projection Step).map (Readback.Obstruction.targetPacked label b) := by
  let θ := Tm.consSubst (.unit : Tm signature.Instr) Tm.var
  have hθ : ∀ ⦃i A⦄, At [U] i A → Tm.BranchValue [U] (θ i) A := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .unit
    | succ i => simp [At] at hi
  have h : Eqv [U] (Readback.Obstruction.source label b) (Readback.Obstruction.target label b) Exits := by
    cases b
    · exact (operand_beta label false (left_typed [U]) (right_typed [U])).substVars (θ := θ) hθ
    · exact (operand_beta label true (left_typed [U]) (right_typed [U])).substVars (θ := θ) hθ
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Step _ _).mpr
    (h.lsubstPost (Readback.Obstruction.source_typed label b) (Readback.Obstruction.target_typed label b)
      (fun _ _ hi => (packExits_valueFamily (Φ := signature.Instr) [U] Exits hi).hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryCaseOperandReplay
