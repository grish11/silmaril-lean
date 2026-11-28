module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms

/-! A guarded producer updates state before an effectful continuation. The
producer can replay a backedge, and the continuation only runs at state one. -/

open CategoryTheory
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches compLSubst)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofRegion_comp)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
open Silmaril.Isotope.Morphism.SSAIter (envOfBound)

namespace LambdaSSAUBPaperCategoryRegression

private inductive Instr where
  | choose | check

private abbrev τ := Ty Empty
private abbrev U : τ := .unit
private abbrev S : τ := .coprod U U

local instance : HasTy Instr τ := ⟨fun _ => U, fun
  | .choose => S
  | .check => U⟩

private abbrev fixture : Shape.Model Instr ([] : List τ) where
  raw := {
    α := Unit
    σ := Nat
    instr := fun f a s v t => match f with
      | .choose => a = .unit ∧ (v = .inl .unit ∨ v = .inr .unit) ∧ t = s + 1
      | .check => a = .unit ∧ s = 1 ∧ v = .unit ∧ t = s + 2
    faults := fun f _ s t => match f with
      | .choose => t = s + 10
      | .check => s = 1 ∧ t = 7
    prim := fun f _ s => match f with
      | .choose => False
      | .check => s = 1
    bound := Fin.elim0 }
  atomType := fun _ _ => False
  boundTyped i := Fin.elim0 i
  instrTyped := by
    intro f _ _ _ _ _ reply
    cases f with
    | choose =>
      rcases reply with ⟨_, rfl | rfl, _⟩
      · exact .inl .unit
      · exact .inr .unit
    | check =>
      obtain ⟨_, _, rfl, _⟩ := reply
      exact .unit

private abbrev R := LambdaSSA.Region Instr

private abbrev producer : R :=
  .cfg (.br 0 .unit) 1 (fun _ =>
    .let₁ (.op .choose .unit) (.case (.var 0) (.br 0 .unit) (.br 1 .unit)))

private abbrev consumer : R := .let₁ (.op .check (.var 0)) (.br 0 (.var 0))

private theorem hp : ValueBranches [U] producer [U] :=
  .cfg (fun _ : Fin 1 => U) (.br (ℓ := 0) rfl .unit) (fun _ =>
    .let₁ (.op (f := Instr.choose) .unit)
      (.case (.var (i := 0) rfl) (.br (ℓ := 0) rfl .unit) (.br (ℓ := 1) rfl .unit)))

private theorem hq : ValueBranches [U] consumer [U] :=
  .let₁ (.op (f := Instr.check) (.var (i := 0) rfl)) (.br (ℓ := 0) rfl (.var (i := 0) rfl))

private theorem family : LambdaSSA.Region.LSubst.ValueFamily ([] : List τ) [U] [U] (fun _ => consumer) :=
  fun _ _ atSlot => (List.mem_singleton.mp (List.mem_of_getElem? atSlot)).symm ▸ hq

private abbrev composed : R := compLSubst (fun _ => producer) (fun _ => consumer) 0
private theorem hc : ValueBranches [U] composed [U] := hp.lsubst (family.liftVars U)

private noncomputable def observation : Behaviour 1 Unit Nat :=
  ((singletonInterpretation fixture).map (ofRegion hp) ≫
    (singletonInterpretation fixture).map (ofRegion hq)).run (0 : Fin 1) ⟨.unit, .unit⟩ 0

private theorem observation_native :
    observation = Shape.denote (.native ⟨composed, hc.hasType⟩) (fixture.extend .unit) 0 := by
  unfold observation
  rw [← Functor.map_comp, ofRegion_comp hp hq hc]
  exact singletonInterpretation_map_ofRegion fixture hc .unit 0

private abbrev runtime := envOfBound (fixture.extend (A := U) .unit).raw.bound
private abbrev block : R := .let₁ (.op .choose .unit)
  (.case (.var 0) (.br 0 .unit) (.let₁ (.op .check .unit) (.br 1 (.var 0))))

private theorem comp_returns_at_final_state : observation.Ordinary (.ret (0 : Fin 1) .unit 3) := by
  rw [observation_native]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change Region.Eval fixture.raw.instr runtime (.cfg (.br 0 .unit) 1 (fun _ => block)) 0 0 .unit 3
  exact .cfg (.br .unit) (.step (by decide)
    (.let₁ (.op .unit ⟨rfl, .inr rfl, rfl⟩) (.case_inr .var
      (.let₁ (.op .unit ⟨rfl, rfl, rfl, rfl⟩) (.br .var)))) (.exit (by decide)))

private theorem comp_faults_in_producer : observation.Ordinary (.fault 10) := by
  rw [observation_native]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change Region.Fault fixture.raw.instr fixture.raw.faults runtime
    (.cfg (.br 0 .unit) 1 (fun _ => block)) 0 10
  exact .cfg_follow (.br .unit) (.body (by decide) (.let₁_arg (.op_fault .unit rfl)))

private theorem comp_faults_in_continuation : observation.Ordinary (.fault 7) := by
  rw [observation_native]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change Region.Fault fixture.raw.instr fixture.raw.faults runtime
    (.cfg (.br 0 .unit) 1 (fun _ => block)) 0 7
  exact .cfg_follow (.br .unit) (.body (by decide)
    (.let₁_body (.op .unit ⟨rfl, .inr rfl, rfl⟩) (.case_inr .var (.let₁_arg (.op_fault .unit ⟨rfl, rfl⟩)))))

private theorem comp_primitive_divergence : observation.Ordinary .diverge := by
  rw [observation_native]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change External.Diverges fixture.raw.instr fixture.raw.prim (.region runtime
    (.cfg (.br 0 .unit) 1 (fun _ => block)) 0)
  exact .fold_core (.cfg_follow (.br .unit) (.fold_core (.follow_body (by decide)
    (.fold_core (.let₁ (.op .unit ⟨rfl, .inr rfl, rfl⟩)
      (.fold_core (.case_inr .var (.fold (.let₁_arg (.primitive .unit rfl))))))))))

private theorem comp_internal_replay : observation.Ordinary .diverge := by
  rw [observation_native]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change External.Diverges fixture.raw.instr fixture.raw.prim (.region runtime
    (.cfg (.br 0 .unit) 1 (fun _ => block)) 0)
  apply External.Diverges.of_internal
  apply Diverges.fold
  apply DivergenceStep.cfg_follow (Region.Eval.br Tm.Eval.unit)
  refine Diverges.coinduct (fun c => ∃ s, c = .follow runtime (fun _ : Fin 1 => block) 0 .unit s) ?_ ⟨0, rfl⟩
  rintro _ ⟨s, rfl⟩
  exact .follow_next (by decide) (.let₁ (.op .unit ⟨rfl, .inl rfl, rfl⟩) (.case_inl .var (.br .unit))) ⟨s + 1, rfl⟩

#print axioms interpretation
#print axioms singletonInterpretation
#print axioms comp_returns_at_final_state
#print axioms comp_faults_in_producer
#print axioms comp_faults_in_continuation
#print axioms comp_primitive_divergence
#print axioms comp_internal_replay

end LambdaSSAUBPaperCategoryRegression
