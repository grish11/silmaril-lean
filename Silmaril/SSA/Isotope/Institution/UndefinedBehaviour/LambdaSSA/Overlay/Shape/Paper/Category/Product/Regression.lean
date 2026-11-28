module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Product.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

/-! The installed fixed-factor arrows retain both tags. Incrementing and
doubling the shared state in different orders yields different states. -/

open CategoryTheory
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion whiskerLeft whiskerRight pairArrows PureReturn)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category (singlePayload pairPayload splitPair valueArrow returnPayload repackage comp_run)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound_agrees)

namespace LambdaSSAUBPaperProductRegression

private inductive Instr where
  | increment | double

private abbrev τ := Ty Empty
private abbrev Flag : τ := .coprod .unit .unit
private abbrev Pair : τ := .product Flag Flag

local instance : HasTy Instr τ := ⟨fun _ => Flag, fun _ => Flag⟩
local instance : HasEff Instr Unit := ⟨fun _ => ()⟩

private def update (f : Instr) (s : Nat) : Nat :=
  match f with
  | .increment => s + 1
  | .double => s * 2

private abbrev fixture : Shape.Model Instr ([] : List τ) where
  raw := {
    α := Unit
    σ := Nat
    instr := fun f a s b t => b = a ∧ t = update f s
    faults := fun _ _ _ _ => False
    prim := fun _ _ _ => False
    bound := Fin.elim0 }
  atomType := fun _ _ => False
  boundTyped i := Fin.elim0 i
  instrTyped := by rintro _ _ _ _ _ typed ⟨rfl, _⟩; exact typed

private abbrev Payload := singlePayload (atomType := fixture.atomType)

private abbrev region (f : Instr) : LambdaSSA.Region Instr :=
  .let₁ (.op f (.var 0)) (.br 0 (.var 0))

private theorem region_typed (f : Instr) : ValueBranches [Flag] (region f) [Flag] :=
  .let₁ (.op (f := f) (.var (i := 0) rfl)) (.br (ℓ := 0) rfl (.var (i := 0) rfl))

private def arrow (f : Instr) : ofType (Φ := Instr) Flag ⟶ ofType Flag :=
  ofRegion (region_typed f)

private noncomputable def run {A B : τ} (f : ofType (Φ := Instr) A ⟶ ofType B) (a : Payload A) (s : Nat) :
    Behaviour 1 Unit Nat :=
  ((singletonInterpretation fixture).map f).run (0 : Fin 1) ⟨a.val, a.property⟩ s

private theorem run_arrow (f : Instr) (a : Payload Flag) (s : Nat) :
    run (arrow f) a s = returnPayload a.val (update f s) := by
  unfold run arrow
  refine (singletonInterpretation_map_ofRegion fixture (region_typed f) a.property s).trans ?_
  apply WithTop.coe_inj.mpr
  apply Set.ext
  intro o
  rw [mem_nativeOutcomes_iff (M := (fixture.extend a.property).raw) _
    ((envOfBound_agrees fixture.raw.bound).extend a.val) s o, Set.mem_singleton_iff]
  cases o with
  | ret i b t =>
    have hi := Fin.eq_zero i
    subst i
    constructor
    · intro run
      cases run with
      | let₁ first last =>
        cases first with
        | op arg exec =>
          cases arg
          obtain ⟨rfl, rfl⟩ := exec
          cases last with | br value => cases value; rfl
    · intro same
      obtain ⟨_, rfl, rfl⟩ := Outcome.ret.inj same
      exact .let₁ (.op .var ⟨rfl, rfl⟩) (.br .var)
  | fault t =>
    constructor
    · intro run
      cases run with
      | let₁_arg arg =>
        cases arg with
        | op_arg arg => cases arg
        | op_fault _ no => exact no.elim
      | let₁_body _ body => cases body with | br arg => cases arg
    · intro eq
      cases eq
  | diverge =>
    constructor
    · intro run
      cases (show External.Diverges fixture.raw.instr fixture.raw.prim _ from run).unfold with
      | let₁_arg arg =>
        cases arg with
        | op_arg arg => cases arg
        | primitive _ no => exact no.elim
      | core step =>
        cases step with
        | let₁ _ body =>
          cases body.unfold with
          | core step => cases step
          | br arg => cases arg
    · intro eq
      cases eq

private def leftStep : ofType (Φ := Instr) Pair ⟶ ofType Pair :=
  whiskerRight (arrow .increment) (ofType Flag)

private def rightStep : ofType (Φ := Instr) Pair ⟶ ofType Pair :=
  whiskerLeft (ofType Flag) (arrow .double)

private theorem left_run (l r : Payload Flag) (s : Nat) :
    run leftStep (pairPayload l r) s = returnPayload (pairPayload l r).val (s + 1) := by
  unfold run leftStep
  refine (congrArg (fun arr => arr.run (0 : Fin 1) ⟨(pairPayload l r).val, (pairPayload l r).property⟩ s)
    (singleton_map_whiskerRight fixture (arrow .increment) Flag)).trans ?_
  change repackage (run (arrow .increment) l s) (fun b => .pair b r.val) = _
  rw [run_arrow]
  exact return_bind 0 l.val (s + 1) _

private theorem right_run (l r : Payload Flag) (s : Nat) :
    run rightStep (pairPayload l r) s = returnPayload (pairPayload l r).val (s * 2) := by
  unfold run rightStep
  refine (congrArg (fun arr => arr.run (0 : Fin 1) ⟨(pairPayload l r).val, (pairPayload l r).property⟩ s)
    (singleton_map_whiskerLeft fixture Flag (arrow .double))).trans ?_
  change repackage (run (arrow .double) r s) (.pair l.val) = _
  rw [run_arrow]
  exact return_bind 0 r.val (s * 2) _

private theorem run_comp_return (f g : ofType (Φ := Instr) Pair ⟶ ofType Pair)
    (a : Payload Pair) (s t : Nat) (returned : run f a s = returnPayload a.val t) :
    run (f ≫ g) a s = run g a t := by
  let F := singletonInterpretation fixture
  refine (congrArg (fun arr => arr.run (0 : Fin 1) ⟨a.val, a.property⟩ s) (F.map_comp f g)).trans ?_
  refine (comp_run (F.map f) (F.map g) (0 : Fin 1) ⟨a.val, a.property⟩ s).trans ?_
  change (run f a s).bind (F.map g).total = run g a t
  rw [returned]
  exact (return_bind 0 a.val t _).trans ((F.map g).total_typed (0 : Fin 1) ⟨a.val, a.property⟩ t)

private abbrev input : Payload Pair :=
  pairPayload (⟨.inl .unit, .inl .unit⟩ : Payload Flag) ⟨.inr .unit, .inr .unit⟩

private theorem left_then_right :
    run (leftStep ≫ rightStep) input 1 = returnPayload input.val 4 :=
  (run_comp_return _ _ input 1 2 (left_run _ _ 1)).trans (right_run _ _ 2)

private theorem right_then_left :
    run (rightStep ≫ leftStep) input 1 = returnPayload input.val 3 :=
  (run_comp_return _ _ input 1 2 (right_run _ _ 1)).trans (left_run _ _ 2)

private theorem paired_projections (s : Nat) :
    run (pairArrows (ofRegion (productSndBranches Flag Flag)) (ofRegion (productFstBranches Flag Flag))) input s =
      returnPayload (.pair (.inr .unit) (.inl .unit)) s :=
  congrArg (fun arr => arr.run (0 : Fin 1) ⟨input.val, input.property⟩ s)
    (singleton_map_pairArrows_value fixture _ _ (fun p => (splitPair p).2) (fun p => (splitPair p).1)
      (singleton_map_productSnd fixture Flag Flag) (singleton_map_productFst fixture Flag Flag))

private theorem effect_annotation_allows_state_change :
    PureReturn () (arrow .increment) ∧
      ¬ ∃ f : Payload Flag → Payload Flag, (singletonInterpretation fixture).map (arrow .increment) = valueArrow f := by
  refine ⟨⟨.op .increment (.var 0), .op (.var (i := 0) rfl), .op rfl .var, rfl⟩, ?_⟩
  rintro ⟨f, same⟩
  let a : Payload Flag := ⟨.inl .unit, .inl .unit⟩
  have runSame := congrArg (fun arr => arr.run (0 : Fin 1) ⟨a.val, a.property⟩ 0) same
  change run (arrow .increment) a 0 = returnPayload (f a).val 0 at runSame
  rw [run_arrow] at runSame
  have outcomes := WithTop.coe_inj.mp runSame
  have returned : Outcome.ret (0 : Fin 1) a.val 1 ∈ ({Outcome.ret 0 (f a).val 0} : Set (Outcome 1 Unit Nat)) :=
    outcomes ▸ Set.mem_singleton _
  cases (Outcome.ret.inj (Set.mem_singleton_iff.mp returned)).2.2

#print axioms singleton_map_productFst
#print axioms singleton_map_productSnd
#print axioms singleton_map_pairArrows_value
#print axioms singleton_map_returnTerm_branchValue
#print axioms singleton_map_whiskerLeft
#print axioms singleton_map_whiskerRight
#print axioms left_then_right
#print axioms right_then_left
#print axioms paired_projections
#print axioms effect_annotation_allows_state_change

end LambdaSSAUBPaperProductRegression
