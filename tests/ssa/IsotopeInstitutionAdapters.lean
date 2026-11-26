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

end Silmaril.Isotope.Institution.Adapters.Tests
