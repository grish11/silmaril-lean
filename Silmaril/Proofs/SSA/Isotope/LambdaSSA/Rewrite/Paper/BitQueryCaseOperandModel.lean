module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.WithCaseOperandBeta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Obstruction.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # The selected term, opcode and region arrows coincide -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryCaseOperandModel

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (caseWithContext_inr)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel case_inl_context extend_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind caseWithContext extend)
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.RequestTree
open Paper.WithCaseBind.BitQuery.RequestTree.Readback.WithCaseOperandBeta
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory (toUnit comp_toUnit_assoc)
open scoped MonoidalCategory

universe u v x y
variable {V : Type u} {C : Type v} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) (M : TypeModel (Ty Empty) V)
  [InstructionModel J M signature.Instr]

private noncomputable def literalMap (E : V) : Bool → (E ⟶ M.obj Bit)
  | false => (toUnit E ≫ M.unitIso.inv) ≫ (coprod.inl ≫ (M.coprodIso U U).inv)
  | true => (toUnit E ≫ M.unitIso.inv) ≫ (coprod.inr ≫ (M.coprodIso U U).inv)

section Term

variable [DistributiveFreydCategory J]

set_option backward.isDefEq.respectTransparency false in
private theorem literal_denotes (Γ : List (Ty Empty)) (b : Bool) :
    Denotes J M ((constructorBit_value (Γ := Γ) b .unit).hasType) (J.map (literalMap M (ctxObj M Γ) b)) := by
  cases b
  · unfold literalMap
    rw [J.map_comp]
    exact .inl .unit
  · unfold literalMap
    rw [J.map_comp]
    exact .inr .unit

omit [InstructionModel J M signature.Instr] in
private theorem drop_literal {E : V} (p : E ⟶ M.obj U) (b : Bool) :
    extend J (J.map p) ≫ J.map (literalMap M (E ⊗ M.obj U) b) =
      J.map (literalMap M E b) := by
  rw [extend_map, ← J.map_comp]
  cases b <;> simp only [literalMap, Category.assoc, comp_toUnit_assoc]

end Term

section Region

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

set_option backward.isDefEq.respectTransparency false in
theorem operand_denotes
    {Γ : List (Ty Empty)} {payload : Tm signature.Instr} (b : Bool)
    (h : Tm.BranchValue Γ payload U) (p : ctxObj M Γ ⟶ M.obj U)
    (hval : Denotes J M h.hasType (J.map p)) :
    ∃ f, Denotes J M (operand_typed b h) f ∧
      Denotes J M ((constructorBit_value (Γ := Γ) b .unit).hasType) f := by
  refine ⟨_, ?_, literal_denotes J M Γ b⟩
  let dl := literal_denotes J M (U :: Γ) false
  let dr := literal_denotes J M (U :: Γ) true
  cases b
  · have d := Denotes.case (Denotes.inl (B := U) hval) dl dr
    simp only [Category.assoc, ← J.map_comp, Iso.inv_hom_id, Category.comp_id] at d
    rw [J.map_comp, case_inl_context J] at d
    change Denotes J M (operand_typed false h)
      (extend J (J.map p) ≫ J.map (literalMap M (ctxObj M Γ ⊗ M.obj U) false)) at d
    rwa [drop_literal J M p false] at d
  · have d := Denotes.case (Denotes.inr (A := U) hval) dl dr
    simp only [Category.assoc, ← J.map_comp, Iso.inv_hom_id, Category.comp_id] at d
    rw [J.map_comp, caseWithContext_inr J] at d
    change Denotes J M (operand_typed true h)
      (extend J (J.map p) ≫ J.map (literalMap M (ctxObj M Γ ⊗ M.obj U) true)) at d
    rwa [drop_literal J M p true] at d

theorem region_denotes {Γ L : List (Ty Empty)} {payload : Tm signature.Instr}
    (label b : Bool) (h : Tm.BranchValue Γ payload U) (p : ctxObj M Γ ⟶ M.obj U)
    (hval : Denotes J M h.hasType (J.map p)) {l r : Region signature.Instr}
    (hl : ValueBranches (Bit :: Γ) l L) (hr : ValueBranches (Bit :: Γ) r L) :
    ∃ f, RegionDenotes J M (source_typed label b h hl hr).hasType f ∧
      RegionDenotes J M (target_typed label b hl hr).hasType f := by
  obtain ⟨_, d, e⟩ := operand_denotes J M b h p hval
  obtain ⟨_, dl⟩ := regionDenotes_exists J M hl.hasType
  obtain ⟨_, dr⟩ := regionDenotes_exists J M hr.hasType
  exact ⟨_, .case (.op d) dl dr, .case (.op e) dl dr⟩

theorem step_denotes {Γ L : List (Ty Empty)} {r s : Region signature.Instr} (h : Step Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  cases h with
  | reduce label b hl hs =>
    exact region_denotes J M label b (.var (i := 0) rfl) (lookup M 0 rfl) (.var rfl) hl hs

/-- Construct the common arrow at the literal packed endpoints from #4812. -/
theorem closed_packed_denotes (label b : Bool) :
    ∃ f,
      RegionDenotes J M (Readback.Obstruction.source_typed label b).packExits.hasType f ∧
      RegionDenotes J M (Readback.Obstruction.target_typed label b).packExits.hasType f := by
  have l : ValueBranches [Bit, U] (.br 0 (.inl (.var 0)) : Region signature.Instr) [packedExitType Exits] :=
    .br (ℓ := 0) rfl (.inl (.var (i := 0) rfl))
  have r : ValueBranches [Bit, U] (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr) [packedExitType Exits] :=
    .br (ℓ := 0) rfl (.inr (.inl (.var (i := 0) rfl)))
  exact region_denotes J M label b .unit (toUnit (ctxObj M [U]) ≫ M.unitIso.inv) .unit l r

end Region

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryCaseOperandModel
