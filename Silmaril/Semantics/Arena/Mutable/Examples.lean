module

import Silmaril.Semantics.Arena.Mutable.Thms

namespace Silmaril.Semantics.Arena.Mutable.Examples

open Silmaril.Semantics.Arena

private def cells : Dense 3 Nat Nat := ⟨#[some ⟨some 7, some 42⟩, some ⟨none, none⟩, none], rfl⟩
private def array : Access (Dense 3 Nat Nat) Nat Nat Fault := Access.array 3

example : array.read cells 0 = some (some 42) ∧ array.read cells 1 = some none ∧ array.read cells 2 = none := by
  decide

example : ((array.change 1 (.insert 99)).commit cells).1 = .error .occupied := rfl
example : ((array.change 2 (.replace 99)).commit cells).1 = .error .vacant := rfl
example : ((array.change 3 .reserve).commit cells).1 = .error .outOfBounds := rfl

example : ((array.change 0 (.replace 99) cells).map fun (_, state) => state.read 0) =
    .ok (some (⟨none, some 99⟩ : Slot Nat Nat)) := rfl

example : ((array.change 1 (.replace 99) cells).map fun (_, state) => array.read state 1) =
    .ok (some (some 99)) := rfl

example : ((array.change 0 .remove cells).map fun (_, state) => array.read state 0) = .ok none := rfl

example :
    let transaction := (array.change 2 (.insert 99)).bind fun _ => array.change 1 (.insert 100)
    let (result, final) := transaction.commit cells
    result = .error .occupied ∧ array.read final 2 = none := by
  exact ⟨rfl, rfl⟩

example : ((Growing.allocate none (⟨3, cells⟩ : Growing Nat Nat)).map fun (key, state) =>
    (key, state.read key, state.read 2)) = .ok (3, some none, none) := rfl

private def stringArena : State String Nat Nat := State.empty

example : ((Access.raw.change "directory" (.insert 41) stringArena).map fun (_, state) =>
    (Access.raw.read state "directory", Access.raw.read state "other")) = .ok (some (some 41), none) := rfl

end Silmaril.Semantics.Arena.Mutable.Examples
