module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Thms

/-! Matching the tag and payload of a repeat does not suffice if its final
machine state is discarded. Identical repeats allow an added fault while
retaining the original return. A shifted repeat reaches the fault instead. -/

open CategoryTheory
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion iterateSum)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
  (singlePayload iterationGraph tagIterationOutcome)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
open Silmaril.Isotope.Morphism.SSAIter (envOfBound_agrees)

namespace LambdaSSAUBPaperIterationRefinementRegression

private abbrev U : Ty Empty := .unit
private abbrev Request := Nat × Bool
private abbrev original : Request := (1, false)
private abbrev wider : Request := (1, true)
private abbrev shifted : Request := (2, false)

local instance : HasTy Request (Ty Empty) := ⟨fun _ => U, fun _ => .coprod U U⟩

private def returns (f : Request) (s : Nat) (a : Value Unit) (t : Nat) : Prop :=
  (s = 0 ∧ a = .inr .unit ∧ t = f.1) ∨ (s = 1 ∧ a = .inl .unit ∧ t = 1)

private def faults (f : Request) (s t : Nat) : Prop :=
  (s = 2 ∨ s = 1 ∧ f.2 = true) ∧ t = s + 10

private abbrev fixture : Shape.Model Request ([] : List (Ty Empty)) where
  raw := {
    α := Unit
    σ := Nat
    instr := fun f a s b t => a = .unit ∧ returns f s b t
    faults := fun f a s t => a = .unit ∧ faults f s t
    prim := fun _ _ _ => False
    bound := Fin.elim0 }
  atomType := fun _ _ => False
  boundTyped i := Fin.elim0 i
  instrTyped := by
    rintro _ _ _ _ _ _ ⟨_, (⟨_, rfl, _⟩ | ⟨_, rfl, _⟩)⟩
    · exact .inr .unit
    · exact .inl .unit

private abbrev body (f : Request) : LambdaSSA.Region Request :=
  .let₁ (.op f (.var 0)) (.br 0 (.var 0))

private theorem body_typed (f : Request) : ValueBranches [U] (body f) [.coprod U U] :=
  .let₁ (.op (f := f) (.var (i := 0) rfl)) (.br (ℓ := 0) rfl (.var (i := 0) rfl))

private abbrev arrow (f : Request) : ofType (Φ := Request) U ⟶ ofType (.coprod U U) :=
  ofRegion (body_typed f)

private abbrev input : singlePayload (atomType := fixture.atomType) U := ⟨.unit, .unit⟩
private abbrev bound := (fixture.extend (A := U) .unit).raw
private abbrev typed (f : Request) : LambdaSSA.UB.Typed (Φ := Request) [U] [.coprod U U] :=
  ⟨body f, (body_typed f).hasType⟩

private noncomputable abbrev atStep (f : Request) (s : Nat) : Behaviour 1 Unit Nat :=
  WithTop.some (nativeOutcomes (typed f) bound s)

private noncomputable abbrev seen (f : Request) := (singletonInterpretation fixture).map (arrow f)
private noncomputable abbrev graph (f : Request) : Feedback.Run [U] [U] Unit Nat :=
  iterationGraph (seen f) input

private noncomputable abbrev loop (f : Request) : Behaviour 1 Unit Nat :=
  ((singletonInterpretation fixture).map (iterateSum (arrow f))).run (0 : Fin 1) input 0

private theorem step_ordinary (f : Request) (s : Nat) (o : Outcome 1 Unit Nat) :
    (atStep f s).Ordinary o ↔
      match o with
      | .ret _ a t => returns f s a t
      | .fault t => faults f s t
      | .diverge => False := by
  have raw : (atStep f s).Ordinary o ↔ o ∈ nativeOutcomes (typed f) bound s :=
    ⟨fun h => h.2, fun h => ⟨WithTop.coe_ne_top, h⟩⟩
  rw [raw, mem_nativeOutcomes_iff _ (envOfBound_agrees bound.bound)]
  cases o with
  | ret i a t =>
    have hi := Fin.eq_zero i
    subst i
    constructor
    · intro h
      cases h with
      | let₁ arg rest =>
        cases rest with
        | br var =>
          cases var
          cases arg with
          | op arg result =>
            cases arg
            exact result.2
    · intro h
      exact Region.Eval.let₁ (.op .var ⟨rfl, h⟩) (.br .var)
  | fault t =>
    constructor
    · intro h
      cases h with
      | let₁_arg arg =>
        cases arg with
        | op_fault arg fault =>
          cases arg
          exact fault.2
        | op_arg sub => cases sub
      | let₁_body _ rest =>
        cases rest with | br var => cases var
    · intro h
      exact Region.Fault.let₁_arg (.op_fault .var ⟨rfl, h⟩)
  | diverge =>
    refine ⟨?_, False.elim⟩
    intro h
    cases h.unfold with
    | let₁_arg arg => exact arg.false
    | core core =>
      cases core with
      | let₁ _ rest =>
        cases rest.unfold with
        | br arg => exact arg.false
        | core core => cases core

private theorem pointwise_wider (s : Nat) : atStep original s ≤ atStep wider s := by
  apply WithTop.coe_le_coe.mpr
  intro o ho
  have h := (step_ordinary original s o).mp ⟨WithTop.coe_ne_top, ho⟩
  apply ((step_ordinary wider s o).mpr ?_).2
  cases o with
  | ret => exact h
  | fault =>
    obtain ⟨state | impossible, final⟩ := h
    · exact ⟨.inl state, final⟩
    · cases impossible.2
  | diverge => exact h

private theorem ordered_iterator : loop original ≤ loop wider := by
  apply singleton_map_iterateSum_mono fixture (arrow original) input 0
  rintro ⟨_, shape⟩ s
  cases shape
  exact pointwise_wider s

private theorem block_ordinary (f : Request) (s : Nat) (o : Outcome 2 Unit Nat) :
    (graph f (.block 0 .unit s)).Ordinary o ↔ (atStep f s).Ordinary (tagIterationOutcome o) := by
  change Behaviour.Ordinary ((seen f).total (0 : Fin 1) input.val s |>.map
    (Set.preimage tagIterationOutcome)) o ↔ _
  rw [Shape.Category.Arrow.total_typed (seen f) (0 : Fin 1) input s]
  exact ⟨fun h => ⟨WithTop.coe_ne_top, h.2⟩, fun h => ⟨WithTop.coe_ne_top, h.2⟩⟩

private theorem reach_repeat (f : Request) : Feedback.Reaches (graph f) (.entry 0) (.block 0 .unit f.1) := by
  apply Relation.ReflTransGen.tail (b := .block 0 .unit 0)
  · exact .single (.branch ⟨WithTop.coe_ne_top, rfl⟩)
  · exact .branch ((block_ordinary f 0 _).mpr ((step_ordinary f 0 _).mpr (.inl ⟨rfl, rfl, rfl⟩)))

private theorem original_return : (loop original).Ordinary (.ret 0 .unit 1) :=
  (singleton_iterateSum_ordinary_iff fixture _ input 0 _).mpr
    (.inl ⟨_, reach_repeat original,
      (block_ordinary original 1 _).mpr ((step_ordinary original 1 _).mpr (.inr ⟨rfl, rfl, rfl⟩))⟩)

private theorem wider_fault : (loop wider).Ordinary (.fault 11) :=
  (singleton_iterateSum_ordinary_iff fixture _ input 0 _).mpr
    (.inl ⟨_, reach_repeat wider,
      (block_ordinary wider 1 _).mpr ((step_ordinary wider 1 _).mpr ⟨.inr ⟨rfl, rfl⟩, rfl⟩)⟩)

private theorem shifted_fault : (loop shifted).Ordinary (.fault 12) :=
  (singleton_iterateSum_ordinary_iff fixture _ input 0 _).mpr
    (.inl ⟨_, reach_repeat shifted,
      (block_ordinary shifted 2 _).mpr ((step_ordinary shifted 2 _).mpr ⟨.inl rfl, rfl⟩)⟩)

private def forgetRepeatState : Outcome 1 Unit Nat → Outcome 1 Unit Nat
  | .ret i (.inr a) _ => .ret i (.inr a) 0
  | o => o

private theorem shifted_matches_without_repeat_states
    (a : singlePayload (atomType := fixture.atomType) U) (s : Nat) (o : Outcome 1 Unit Nat)
    (h : ((seen original).run (0 : Fin 1) a s).Ordinary o) :
    ∃ p, ((seen shifted).run (0 : Fin 1) a s).Ordinary p ∧ forgetRepeatState p = forgetRepeatState o := by
  obtain ⟨_, shape⟩ := a
  cases shape
  have step := (step_ordinary original s o).mp h
  cases o with
  | ret i a t =>
    rcases step with ⟨start, rfl, _⟩ | finished
    · exact ⟨.ret i (.inr .unit) 2, (step_ordinary shifted s _).mpr (.inl ⟨start, rfl, rfl⟩), rfl⟩
    · exact ⟨.ret i a t, (step_ordinary shifted s (.ret i a t)).mpr (.inr finished), rfl⟩
  | fault t => exact ⟨.fault t, (step_ordinary shifted s (.fault t)).mpr step, rfl⟩
  | diverge => exact step.elim

private theorem shifted_reachable {p} (h : Feedback.Reaches (graph shifted) (.entry 0) p) :
    p = .entry 0 ∨ p = .block 0 .unit 0 ∨ p = .block 0 .unit 2 := by
  induction h with
  | refl => exact .inl rfl
  | @tail p q _ edge ih =>
    cases edge with
    | @branch i b s run =>
      have hi := Fin.eq_zero i
      subst i
      rcases ih with rfl | rfl | rfl
      · have eq : Outcome.ret (0 : Fin 2) b s = .ret 0 .unit 0 := run.2
        obtain ⟨_, rfl, rfl⟩ := Outcome.ret.inj eq
        exact .inr (.inl rfl)
      · have ret := (step_ordinary shifted 0 _).mp ((block_ordinary shifted 0 _).mp run)
        rcases ret with ⟨_, tag, rfl⟩ | ⟨impossible, _, _⟩
        · cases tag
          exact .inr (.inr rfl)
        · cases impossible
      · have ret := (step_ordinary shifted 2 _).mp ((block_ordinary shifted 2 _).mp run)
        rcases ret with ⟨impossible, _, _⟩ | ⟨impossible, _, _⟩ <;> cases impossible

private theorem shifted_no_return : ¬ (loop shifted).Ordinary (.ret 0 .unit 1) := by
  intro h
  rcases (singleton_iterateSum_ordinary_iff fixture (arrow shifted) input 0 _).mp h with
    ⟨p, path, finish⟩ | ⟨impossible, _⟩
  · rcases shifted_reachable path with rfl | rfl | rfl
    · have impossible : Outcome.ret (1 : Fin 2) .unit 1 = .ret 0 .unit 0 := finish.2
      cases impossible
    · have ret := (step_ordinary shifted 0 _).mp ((block_ordinary shifted 0 _).mp finish)
      rcases ret with ⟨_, tag, _⟩ | ⟨impossible, _, _⟩
      · cases tag
      · cases impossible
    · have ret := (step_ordinary shifted 2 _).mp ((block_ordinary shifted 2 _).mp finish)
      rcases ret with ⟨impossible, _, _⟩ | ⟨impossible, _, _⟩ <;> cases impossible
  · cases impossible

private theorem ordinary_of_loop_le {f g : Request} {o : Outcome 1 Unit Nat}
    (le : loop f ≤ loop g) (reached : (loop f).Ordinary o) : (loop g).Ordinary o := by
  have ordinary : loop g ≠ ⊤ := singleton_map_ne_top fixture (iterateSum (arrow g)) input 0
  obtain ⟨lower, hl⟩ := WithTop.ne_top_iff_exists.mp reached.1
  obtain ⟨upper, hu⟩ := WithTop.ne_top_iff_exists.mp ordinary
  rw [← hl, ← hu] at le
  rw [← hl] at reached
  exact hu ▸ ⟨WithTop.coe_ne_top, WithTop.coe_le_coe.mp le reached.2⟩

private theorem wider_return : (loop wider).Ordinary (.ret 0 .unit 1) :=
  ordinary_of_loop_le ordered_iterator original_return

private theorem shifting_breaks_refinement : ¬ loop original ≤ loop shifted :=
  fun le => shifted_no_return (ordinary_of_loop_le le original_return)

#print axioms singleton_map_iterateSum_mono
#print axioms singleton_map_iterateSum_mono_of_refines
#print axioms ordered_iterator
#print axioms wider_return
#print axioms wider_fault
#print axioms shifted_fault
#print axioms shifted_matches_without_repeat_states
#print axioms shifting_breaks_refinement

end LambdaSSAUBPaperIterationRefinementRegression
