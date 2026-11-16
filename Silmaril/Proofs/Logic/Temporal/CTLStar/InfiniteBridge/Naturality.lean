module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.InfiniteBridge.Language

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.NNF

theorem Formula.toInfinite_map {A B : Type} (f : A → B) (p : Formula A) :
    (p.map f).toInfinite = p.toInfinite.map f := by
  induction p <;> simp_all [toInfinite, map, LTL.NNF.Formula.map]

theorem Formula.toInfinite_dual {A : Type} (p : Formula A) :
    p.dual.toInfinite = p.toInfinite.dual := by
  induction p <;> simp_all [toInfinite, dual, LTL.NNF.Formula.dual]

end Silmaril.Logic.Temporal.CTLStar.NNF

noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.InfiniteBridge
open CategoryTheory

/-- Actual generalized automaton syntax, with its finite dimensions transported. -/
theorem automaton_map {A B : Type} (f : A → B) (p : NNF.Formula A) :
    HEq (automaton (p.map f)) ((automaton p).map f) := by
  unfold automaton
  rw [NNF.Formula.toInfinite_map]
  exact LTL.Tableau.automaton_map f p.toInfinite

/-- Arbitrary atom maps, including collapse, pull back the whole infinite word. -/
theorem accepts_map {A B : Type} (f : A → B) (p : NNF.Formula A)
    (word : Nat → B → Prop) :
    (automaton (p.map f)).Accepts word ↔ (automaton p).Accepts (fun t a => word t (f a)) := by
  rw [accepts_iff, accepts_iff]
  exact NNF.Formula.holds_map f none word p 0

/-- Equality of the actual emitted scalar syntax under atom/action renaming. -/
theorem formula_map {S T : ModalMu.Signature} (f : S ⟶ T) (p : NNF.Formula S.Atom)
    (a : S.Action) : (formula p a).map f = formula (p.map f.atom) (f.action a) := by
  simp only [formula, LTL.Tableau.formula_map, NNF.Formula.toInfinite_map]

end Silmaril.Logic.Temporal.CTLStar.InfiniteBridge
