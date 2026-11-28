module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Boundary.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.ReturnJoin.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.Boundary

open Region.Paper
open UnaryReturn.Beta.Constructors.Example (source)
open LetCase.LocallyNameless (Equiv HasType)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural
open scoped Silmaril.Isotope.LambdaSSA.Acyclic.Native.Boundary

set_option backward.isDefEq.respectTransparency false

local notation "U" => (Ty.unit : Ty Empty)
local notation "X" => source
local notation "P" => (Ty.product X X)
local notation "β" => (BoundCtx.nil.snoc X)
local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty Empty))

theorem unit_joined_proof : unitReturn.JoinedEqv unitForward := by
  let step : WithUnitEta.Eqv [U] (.br 0 (.unit : Tm Empty)) (.br 0 (.var 0)) [U] :=
    WithUnitEta.branch_unit_eta (.var rfl) rfl
  exact WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed
    (Target := WithCaseAndUnaryReturns.JoinedStep false) (fun h => Or.inl (Or.inr h)) step

private theorem sameTyping (t t' : HasTy Empty (Ty Empty)) : t = t' := by
  cases t
  cases t'
  congr <;> funext f <;> exact f.elim

theorem unit_default_fails_proof : ¬ Region.Paper.Eqv [U] unitReturn.region unitForward.region [U] := by
  change ¬ @Region.Paper.Eqv (Ty Empty) _ Empty (inferInstance : HasTy Empty (Ty Empty))
    [U] unitReturn.region unitForward.region [U]
  rw [sameTyping inferInstance BoundSimulation.Obstruction.instHasTyEmptyTy]
  exact BoundSimulation.Obstruction.unit_eta_fails

theorem pair_joined_fails_proof : ¬ paired.JoinedEqv sequenced := by
  have sameEffects (e e' : HasEff Empty Bool) : e = e' := by
    cases e
    cases e'
    congr
    funext f
    exact f.elim
  change ¬ @Extension.Eqv (Ty Empty) _ Empty (inferInstance : HasTy Empty (Ty Empty))
    (@WithCaseAndUnaryReturns.JoinedStep (Ty Empty) _ Empty (inferInstance : HasTy Empty (Ty Empty))
      Bool (inferInstance : HasEff Empty Bool) false) [X] paired.region sequenced.region [P]
  rw [sameTyping inferInstance BoundSimulation.Obstruction.instHasTyEmptyTy,
    sameEffects inferInstance BoundSimulation.Obstruction.PairSequencing.instHasEffEmptyBool]
  exact BoundSimulation.Obstruction.PairSequencing.case_unary_pair_sequence_fails

private def left : Operand Empty β X :=
  ⟨.let₁ (.bv 0) (.bv 0), .let₁ .bv .bv⟩

private def right : Operand Empty β X := ⟨.bv 0, .bv⟩

private def pairCode : Code Empty β P :=
  .let₁ ⟨_, .pair left.2 right.2⟩ (.br ⟨.bv 0, .bv⟩)

private def seqCode : Code Empty β P :=
  .let₁ left (.let₁ ⟨.bv 1, .bv⟩ (.br ⟨.pair (.bv 1) (.bv 0), .pair .bv .bv⟩))

private theorem pair_native :
    Equiv false Γ₀ β pairCode.toLetCase.1 seqCode.toLetCase.1 P := by
  have hl := left.2.toHasType
  have hr := right.2.toHasType
  have body : HasType Empty Γ₀ (BoundCtx.snoc (BoundCtx.snoc β X) X) (.pair (.bv 1) (.bv 0)) P :=
    .pair .bv .bv
  exact (Equiv.letEta (.pair hl hr)).trans
    ((Equiv.pairEta (.pair hl hr)).symm.trans (Equiv.pairBeta hl hr body))

theorem pair_valid_proof : paired.Valid sequenced :=
  paired.valid_of_code_equiv sequenced pairCode seqCode rfl rfl pair_native

/-- The separated equation is already a checked root step in the existing
constructor-sequencing extension. -/
theorem pair_constructor_proof :
    WithConstructorSequencing.Step [X] paired.region sequenced.region [P] := by
  have old : Tm.BranchValue [X] (Tm.var 0 : Tm Empty) X := .var rfl
  have new : Tm.BranchValue [X, X] (Tm.var 0 : Tm Empty) X := .var rfl
  exact .pair (.let₁ (.value old) (.value new)) (.value old)

theorem pair_reification_fails_proof : ¬ (∀ a b : Operand Empty β P, ReificationReplay a b) := by
  intro replay
  have pg : Region.ValueBranches [X] paired.region [P] :=
    .let₁ (.pair (.let₁ (.var rfl) (.var rfl)) (.var rfl)) (.br rfl (.var rfl))
  have sg : Region.ValueBranches [X] sequenced.region [P] :=
    .let₁ (.let₁ (.var rfl) (.var rfl))
      (.let₁ (.var (i := 1) rfl) (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))
  have pa : pairCode.Admitted := ⟨trivial, trivial⟩
  have sa : seqCode.Admitted := ⟨⟨trivial, trivial⟩, trivial, trivial⟩
  exact pair_joined_fails_proof
    ((paired.joined_roundTrip_at pairCode rfl pa pg).trans
      ((replay _ _ pair_native).trans (sequenced.joined_roundTrip_at seqCode rfl sa sg).symm))

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.Boundary
