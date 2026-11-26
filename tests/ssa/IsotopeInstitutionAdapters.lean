module

import Silmaril.SSA.Isotope.Institution.Adapters.Thms

/-! A case equation distinguishes a deterministic copy from a nondeterministic primitive.
The distinction survives the actual powerset comorphism and a signature reduct. -/

namespace Silmaril.Isotope.Institution.Adapters.Tests

open CategoryTheory Semantics Theory Silmaril.Logic.Institution

abbrev Sorts := Ty Unit
abbrev Bit : Sorts := .base ()
abbrev Val : Sorts → Type := Ty.denote (fun _ => Bool)

inductive Op where
  | copy | choose

def signature : InstrSig Sorts Unit where
  Instr := Op
  hasTy := ⟨fun _ => Bit, fun _ => Bit⟩
  hasEff := ⟨fun _ => ()⟩

def changeOpcode : signature ⟶ signature where
  instr _ := Op.choose
  source _ := rfl
  target _ := rfl
  effect _ := rfl

def model : Powerset.Model Val signature where
  relational := ⟨fun op input output => match op with
    | .copy => output = input
    | .choose => True⟩

def pairing {A B : Type} (a : SetM A) (b : SetM B) : SetM (A × B) :=
  {p | p.1 ∈ a.run ∧ p.2 ∈ b.run}

def context : Ctx Empty Sorts := .nil
def bound : BoundCtx Sorts 1 := .snoc .nil (.coprod Bit Bit)

def equation : Relational.LetCase.Sentence signature context :=
  ⟨⟨1, bound, Bit⟩,
    ⟨.case (.bv 0) (.op Op.copy (.bv 0)) (.bv 0), .case .bv (.op .bv) .bv⟩,
    ⟨.case (.bv 0) (.bv 0) (.bv 0), .case .bv .bv .bv⟩⟩

theorem copy_holds : Relational.LetCase.Sentence.Satisfies model.relational equation := by
  intro γ ρ b
  dsimp [equation, LetCase.LocallyNameless.Derivation.denoteRelation, model]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  cases CoproductModel.coprodEquiv (D := Val) Bit Bit e with
  | inl a =>
      change (∃ x : Bool, x = a ∧ b = x) ↔ b = a
      exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨a, rfl, h⟩⟩
  | inr _ => rfl

theorem choose_fails :
    ¬ Relational.LetCase.Sentence.Satisfies (model.reduct changeOpcode).relational equation := by
  intro h
  let γ : FreeEnv Val context := fun x => nomatch x
  let ρ : BoundEnv Val bound := BoundEnv.snoc (fun i => Fin.elim0 i) (.inl false)
  have result := h γ ρ true
  dsimp [equation, LetCase.LocallyNameless.Derivation.denoteRelation] at result
  obtain ⟨e, he, hout⟩ := result.mp ⟨Sum.inl false, rfl, false, rfl, trivial⟩
  change e = Sum.inl false at he
  subst e
  exact Bool.noConfusion hout

def comparison := Powerset.letCase (ε := Unit) (D := Val) context pairing

theorem native_copy_holds :
    ((Powerset.observation (by decide) (Parallel.Control.case Val Id) context pairing).obj
      signature).Sat model (Powerset.ofLetCase equation) :=
  (comparison.satisfaction signature model equation).mpr copy_holds

theorem native_relabelled_choose_fails :
    ¬ ((Powerset.observation (by decide) (Parallel.Control.case Val Id) context pairing).obj
      signature).Sat model ((Powerset.ofLetCase equation).map changeOpcode) := by
  intro h
  apply choose_fails
  apply (Powerset.ofLetCase_sat pairing (model.reduct changeOpcode) equation).mp
  exact (satisfaction_condition (Powerset.observation (by decide)
    (Parallel.Control.case Val Id) context pairing) changeOpcode model
      (Powerset.ofLetCase equation)).mp h

section Iteration

open LetIter.ProofRelevant.Semantics (TypeModel)

private def coerceValue : {A B : Sorts} → Ty.Subty A B → Val A → Val B
  | _, _, .refl _, x => x
  | _, _, .trans f g, x => coerceValue g (coerceValue f x)
  | _, _, .product f g, (x, y) => (coerceValue f x, coerceValue g y)
  | _, _, .coprod f g, x => Sum.map (coerceValue f) (coerceValue g) x
  | _, _, .empty _, x => x.elim
  | _, _, .unit _, _ => PUnit.unit

local instance : TypeModel Sorts where
  interp := Val
  productEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun _ => rfl, fun _ => rfl⟩
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => x.elim, fun x => x.elim⟩
  coe := coerceValue

local instance : Bot Bool := ⟨false⟩

private def loopSignature : InstrSig Sorts Bool where
  Instr := Unit
  hasTy := ⟨fun _ => Bit, fun _ => coprod unit Bit⟩
  hasEff := ⟨fun _ => false⟩

private def loopBound : BoundCtx Sorts 1 := .snoc .nil Bit

private def feedback (returns : Bool) (state : Bool) : PUnit ⊕ Bool :=
  if returns && state then .inl PUnit.unit else .inr true

private def loopModel (returns : Bool) : UpperPowerset.Model loopSignature where
  instructions :=
    { denote := fun _ a => pure (feedback returns a)
      denotePure := fun _ _ => feedback returns
      denote_pure := fun _ _ _ => rfl }

private def loopEquation : Relational.LetIter.Sentence loopSignature context :=
  ⟨⟨1, loopBound, unit⟩, ⟨.iter (.bv 0) (.op () (.bv 0)), .iter .bv (.op .bv)⟩, ⟨.unit, .unit⟩⟩

attribute [local instance] LetParIter.nativeProductModel LetParIter.nativeUnitModel
  Iteration.nativeCoproductModel

private theorem returns_in_at_most_two_steps :
    Relational.LetIter.Sentence.Satisfies (UpperPowerset.Model.toRelational.obj (loopModel true)) loopEquation := by
  intro γ ρ b
  change (∃ a : Bool, a = ρ (0 : Fin 1) ∧ Relation.Iterates
    (fun s result => ∃ x, x = s ∧ result = feedback true x) a b) ↔ b = PUnit.unit
  cases b
  refine ⟨fun _ => rfl, fun _ => ⟨ρ (0 : Fin 1), rfl, ?_⟩⟩
  cases ρ (0 : Fin 1)
  · exact .more (a' := true) ⟨false, rfl, rfl⟩ (.done ⟨true, rfl, rfl⟩)
  · exact .done ⟨true, rfl, rfl⟩

private theorem no_successful_step :
    ¬ Relational.LetIter.Sentence.Satisfies (UpperPowerset.Model.toRelational.obj (loopModel false)) loopEquation := by
  intro h
  let γ : FreeEnv Val context := fun x => nomatch x
  let ρ : BoundEnv Val loopBound := BoundEnv.snoc (fun i => Fin.elim0 i) false
  have result := (h γ ρ PUnit.unit).mpr rfl
  change ∃ a : Bool, a = false ∧ Relation.Iterates
    (fun s result => ∃ x, x = s ∧ result = feedback false x) a PUnit.unit at result
  obtain ⟨_, _, run⟩ := result
  refine Relation.Iterates.not_of_no_return (fun _ b ⟨_, _, h⟩ => ?_) run
  change Sum.inl b = Sum.inr true at h
  cases h

/-- The exact feedback equation is satisfied for a two-step return. -/
theorem upper_loop_holds (pair : Elgot.ParallelPairing (SetM : Type → Type)) :
    (UpperPowerset.room pair loopSignature Empty).Sat (loopModel true) (Iteration.ofLetIter loopEquation) :=
  ((UpperPowerset.letIter (ε := Bool) Iteration.visibleEnv_nil_surjective pair).satisfaction
    loopSignature (loopModel true) loopEquation).mpr returns_in_at_most_two_steps

/-- Continuing forever has an empty successful-result set and fails the same equation. -/
theorem upper_loop_fails (pair : Elgot.ParallelPairing (SetM : Type → Type)) :
    ¬ (UpperPowerset.room pair loopSignature Empty).Sat (loopModel false) (Iteration.ofLetIter loopEquation) :=
  fun h => no_successful_step (((UpperPowerset.letIter (ε := Bool) Iteration.visibleEnv_nil_surjective pair).satisfaction
    loopSignature (loopModel false) loopEquation).mp h)

end Iteration
end Silmaril.Isotope.Institution.Adapters.Tests
