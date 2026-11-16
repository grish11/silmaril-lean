module

public import Silmaril.Proofs.Logic.Temporal.Buchi.Automaton.Base.FixedPoint

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.Buchi.Automaton.Base
open ModalMu CategoryTheory

theorem disjoin_map {S T : Signature} (f : S ⟶ T) {n k : Nat}
    (p : Fin n → Formula S k) :
    (disjoin p).map f = disjoin (fun i => (p i).map f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [disjoin, Formula.map, ih]

theorem next_map {S T : Signature} (f : S ⟶ T) {n k : Nat}
    (A : Symbolic S.Atom n) (a : S.Action) (X : Fin n → Formula S k) (q : Fin n) :
    (next A a X q).map f = next (A.map f.atom) (f.action a) (fun r => (X r).map f) q := by
  unfold next
  rw [disjoin_map]
  congr 1
  funext r
  simp only [Formula.map, Guard.toFormula_map, Symbolic.map]

theorem innerSystem_map {S T : Signature} (f : S ⟶ T) {n : Nat}
    (A : Symbolic S.Atom n) (a : S.Action) :
    (innerSystem A a).map f = innerSystem (A.map f.atom) (f.action a) := by
  classical
  change FiniteVector.System.mk _ = FiniteVector.System.mk _
  congr 1
  funext q
  by_cases hq : q ∈ A.accepting
  · simp only [innerSystem, Symbolic.map, hq, ↓reduceIte, Formula.map, next_map]
  · simp only [innerSystem, Symbolic.map, hq, ↓reduceIte, Formula.map, next_map]

theorem outerSystem_map {S T : Signature} (f : S ⟶ T) {n : Nat}
    (A : Symbolic S.Atom n) (a : S.Action) :
    (outerSystem A a).map f = outerSystem (A.map f.atom) (f.action a) := by
  change FiniteVector.System.mk _ = FiniteVector.System.mk _
  congr 1
  funext q
  change ((innerSystem A a).compile false q).map f = _
  rw [FiniteVector.System.compile_map, innerSystem_map]

/-- Naturality holds as equality of the emitted scalar syntax. -/
theorem coordinate_map {S T : Signature} (f : S ⟶ T) {n : Nat}
    (A : Symbolic S.Atom n) (a : S.Action) (q : Fin n) :
    (coordinate A a q).map f = coordinate (A.map f.atom) (f.action a) q := by
  unfold coordinate
  rw [FiniteVector.System.compile_map, outerSystem_map]

theorem formula_map {S T : Signature} (f : S ⟶ T) {n : Nat}
    (A : Symbolic S.Atom n) (a : S.Action) :
    (formula A a).map f = formula (A.map f.atom) (f.action a) := by
  classical
  unfold formula
  rw [disjoin_map]
  congr 1
  funext q
  by_cases hq : q ∈ A.initial
  · simp only [Symbolic.map, hq, ↓reduceIte, coordinate_map]
  · simp only [Symbolic.map, hq, ↓reduceIte, Formula.map]

end Silmaril.Logic.Temporal.Buchi.Automaton.Base
