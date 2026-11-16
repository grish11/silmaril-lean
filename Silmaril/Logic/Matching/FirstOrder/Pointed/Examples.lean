module

public import Silmaril.Logic.Matching.FirstOrder.Pointed.Propositional

@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder.Pointed.Examples
open CategoryTheory
open Silmaril.Logic.Institution.Examples

/-- An atom denotes a proper nonempty subset of a two-element carrier. -/
def twoState : FirstOrder.Model (propositionalSignature Unit) where
  carrier _ := Bool
  nonempty _ := inferInstance
  operation op := match op with | .atom _ => fun _ => {true}

def atTrue : Model () (propositionalSignature Unit) := ⟨twoState, true⟩
def atFalse : Model () (propositionalSignature Unit) := ⟨twoState, false⟩
def atom : PL.Formula Unit := .var ()
def negAtom : PL.Formula Unit := .imp atom .bot

theorem true_point_matches : atTrue.Satisfies (encodePropositional atom) := by
  rw [encodePropositional_satisfies]
  exact rfl

theorem false_point_does_not_match : ¬ atFalse.Satisfies (encodePropositional atom) := by
  rw [encodePropositional_satisfies]
  exact Bool.false_ne_true

theorem false_point_matches_negation : atFalse.Satisfies (encodePropositional negAtom) := by
  rw [encodePropositional_satisfies]
  exact Bool.false_ne_true

/-- The global core cannot use one Boolean valuation for both a proper subset
and its complement: both global sentences fail in this populated model. -/
theorem both_atom_and_negation_fail_globally :
    ¬ Sentence.Satisfies twoState (closedSentence () (encodePropositional atom)) ∧
    ¬ Sentence.Satisfies twoState (closedSentence () (encodePropositional negAtom)) := by
  constructor
  · intro h
    exact false_point_does_not_match ((global_iff_all_points () twoState _).mp h false)
  · intro h
    have ht := (global_iff_all_points () twoState _).mp h true
    rw [encodePropositional_satisfies] at ht
    exact ht rfl

/-- A nonidentity pointed relational homomorphism; its propositional reduct
sends the false atom valuation to the true atom valuation. -/
def falseToTrue : atFalse ⟶ atTrue where
  base :=
    { map := fun _ _ => true
      operation := by
        intro n inputs output op args result member
        cases op
        exact rfl }
  point := rfl

theorem reduct_arrow_preserves_atom :
    ((pointValuation Unit).obj atFalse).val () → ((pointValuation Unit).obj atTrue).val () :=
  ((pointValuation Unit).map falseToTrue).down ()
end Silmaril.Logic.Matching.FirstOrder.Pointed.Examples
