module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.FiniteScalar.Language

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.FiniteScalar
open LTL.Tableau Buchi.Automaton ModalMu CategoryTheory

theorem pack_map {A B : Type} (s : Shape) (edge : State s → State s → Guard A)
    (last : State s → Guard A) (f : A → B) :
    (pack s edge last).map f = pack s (fun X Y => (edge X Y).map f)
      (fun X => (last X).map f) := rfl

theorem pack_formula_transport {S : ModalMu.Signature} {s t : Shape} (h : s = t)
    (edge : State s → State s → Guard S.Atom) (last : State s → Guard S.Atom)
    (edge' : State t → State t → Guard S.Atom) (last' : State t → Guard S.Atom)
    (he : ∀ X Y, edge' (castState h X) (castState h Y) = edge X Y)
    (ht : ∀ X, last' (castState h X) = last X) (a : S.Action) :
    FiniteAutomaton.formula (pack t edge' last') a =
      FiniteAutomaton.formula (pack s edge last) a := by
  cases h
  have he' : edge' = edge := funext fun X => funext fun Y => he X Y
  have ht' : last' = last := funext fun X => ht X
  cases he'; cases ht'; rfl

/-- Equality of actual emitted syntax under arbitrary atom and action maps. -/
theorem formula_map {S T : ModalMu.Signature} (f : S ⟶ T) (p : NNF.Formula S.Atom)
    (a : S.Action) : (formula p a).map f = formula (p.map f.atom) (f.action a) := by
  rw [formula, FiniteAutomaton.formula_map, formula, automaton, automaton, pack_map]
  exact (pack_formula_transport (FiniteTableau.shape_map f.atom p).symm _ _ _ _
    (FiniteTableau.transition_map f.atom p) (FiniteTableau.terminal_map f.atom p)
    (f.action a)).symm

end Silmaril.Logic.Temporal.CTLStar.FiniteScalar
