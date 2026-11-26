module

import Silmaril.SSA.MLIR.SCF.Parallel.Thms

/-! Checked grouped, empty, and order-sensitive cases for the pure reduction interface. -/

namespace Silmaril.MLIR.SCF.Parallel.Examples

private def strided : IndexSpace := ⟨2, 8, 4, by decide⟩
private def firstTrip : strided.Trip := ⟨0, by decide⟩
private def secondTrip : strided.Trip := ⟨1, by decide⟩

private def carrier : Fin 2 → Type :=
  Fin.cases Nat (fun _ => Bool)

private def grouped : GroupedReduction carrier where
  initial := Fin.cases (10 : Nat) (fun _ => false)
  contribution index := Fin.cases index (fun _ => index == 6)
  combine := Fin.cases Nat.add (fun _ => Bool.or)

private def reversed : strided.Enumeration where
  val := [secondTrip, firstTrip]
  property := by
    rw [show strided.trips = [firstTrip, secondTrip] by decide]
    exact List.Perm.swap firstTrip secondTrip []

private def rightAssociated : Tree (Input strided) :=
  .fork (.leaf .initial) (.fork (.leaf (.trip secondTrip)) (.leaf (.trip firstTrip)))

example : strided.index firstTrip = 2 ∧ strided.index secondTrip = 6 ∧ strided.exitIndex = 10 :=
  ⟨rfl, rfl, rfl⟩

/-- Reversing the contributions and changing the tree preserves both typed results. -/
example : grouped.toReduction.eval strided rightAssociated = grouped.toReduction.denote strided :=
  grouped.eval_eq_denote strided rightAssociated ⟨reversed, rfl⟩
    (Fin.cases ⟨Nat.add_assoc⟩ (fun _ => ⟨Bool.or_assoc⟩))
    (Fin.cases ⟨Nat.add_comm⟩ (fun _ => ⟨Bool.or_comm⟩))

example :
    grouped.toReduction.denote strided 0 = (18 : Nat) ∧
      grouped.toReduction.denote strided 1 = true :=
  ⟨rfl, rfl⟩

private def emptySpace : IndexSpace := ⟨8, 2, 4, by decide⟩

example : grouped.toReduction.denote emptySpace = grouped.initial :=
  grouped.toReduction.denote_of_empty emptySpace (by decide)

private def rightProjection : Reduction Nat := ⟨99, id, fun _ next => next⟩

/-- The initial value is returned for zero trips even with a noncommutative combiner. -/
example : rightProjection.eval emptySpace (.leaf .initial) = 99 :=
  rightProjection.eval_of_empty emptySpace (.leaf .initial) ⟨⟨[], .nil⟩, rfl⟩ (by decide)

example : ¬ Std.Commutative rightProjection.combine := by
  intro comm
  exact (by decide : (2 : Nat) ≠ 6) (comm.comm 6 2)

example : rightProjection.denote strided = 6 := rfl

/-- The reversed tree has a different admissible result from the reference fold. -/
example : rightProjection.Returns strided 2 :=
  ⟨rightAssociated, ⟨reversed, rfl⟩, rfl⟩

example : rightProjection.Returns strided 6 :=
  rightProjection.returns_denote strided

end Silmaril.MLIR.SCF.Parallel.Examples
