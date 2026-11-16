module

public import Silmaril.Proofs.Logic.Temporal.FiniteAutomaton.Soundness

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.FiniteAutomaton
open ModalMu Buchi.Automaton CategoryTheory

theorem system_map {S T : Signature} {n : Nat} (F : Symbolic S.Atom n) (a : S.Action)
    (f : S ⟶ T) : (system F a).map f = system (F.map f.atom) (f.action a) := by
  change FiniteVector.System.mk _ = FiniteVector.System.mk _
  congr 1
  funext q
  simp only [system, Formula.map, Guard.toFormula_map, Base.disjoin_map, Symbolic.map]

/-- Actual scalar syntax commutes with arbitrary atom/action maps. -/
theorem coordinate_map {S T : Signature} {n : Nat} (F : Symbolic S.Atom n) (a : S.Action)
    (f : S ⟶ T) (q : Fin n) :
    (coordinate F a q).map f = coordinate (F.map f.atom) (f.action a) q := by
  rw [coordinate, FiniteVector.System.compile_map, system_map]
  rfl

theorem formula_map {S T : Signature} {n : Nat} (F : Symbolic S.Atom n) (a : S.Action)
    (f : S ⟶ T) : (formula F a).map f = formula (F.map f.atom) (f.action a) := by
  classical
  unfold formula
  rw [Base.disjoin_map]
  congr 1
  funext q
  by_cases hi : q ∈ F.initial
  · simp only [Symbolic.map, hi, ↓reduceIte, coordinate_map]
  · simp only [Symbolic.map, hi, ↓reduceIte, Formula.map]

end Silmaril.Logic.Temporal.FiniteAutomaton
