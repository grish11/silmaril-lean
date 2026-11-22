module

import Silmaril.Semantics.Arena.Cas.Intern.Thms
import Silmaril.Semantics.Arena.Mutable.Thms

namespace Silmaril.Semantics.Arena.Cas.Intern.Examples

private def block (obj : UInt8) : ByteArray := ⟨#[obj]⟩

private def profile : Profile Nat UInt8 := ⟨some ∘ block, fun bytes => some (bytes[0]?.getD 0).toNat⟩

private def arena : State Nat Nat UInt8 where
  slots
  | 0 => some ⟨some 1, some 1⟩
  | 1 => some ⟨some 2, none⟩
  | 3 => some ⟨some 3, some 3⟩
  | _ => none
  blocks name := if name = 1 then some (block 1) else if name = 3 then some (block 3) else none

private def index : Index Nat Nat
  | 1 => some 0
  | 3 => some 3
  | _ => none

example : index.Exact arena := by
  intro name key
  rcases name with _ | _ | _ | _ | name <;>
    rcases key with _ | _ | _ | _ | key <;> simp [index, arena, State.attachedKeys]

example : replaceShared profile index none 0 1 arena = .ok (⟨0, 1⟩, arena) := rfl
example : replaceShared profile index none 0 3 arena = .ok (⟨3, 3⟩, arena) := rfl

example : (replaceShared profile index (some 2) 0 2 arena).map (fun (entry, updated) =>
    (entry, updated.slots 0, updated.slots 1, updated.slots 2, updated.blocks 1, updated.blocks 2)) =
    .ok (⟨2, 2⟩, some ⟨some 1, some 1⟩, some ⟨some 2, none⟩, some ⟨some 2, some 2⟩, some (block 1), some (block 2)) := rfl

example : replaceShared profile index (some 1) 0 2 arena = .error .occupied := rfl
example : replaceShared profile index none 0 2 arena = .error .noCapacity := rfl
example : replaceShared profile index (some 2) 2 2 arena = .error .sourceVacant := rfl
example : replaceShared profile index (some 2) 1 2 arena = .error .sourceUnresident := rfl
example : intern profile (fun _ => some 1) (some 2) 1 arena = .error .staleHit := rfl

example : (intern profile (fun _ => none) (some 2) 1 arena).map
    (fun (_, updated) => (updated.slots.keyName 0, updated.slots.keyName 2)) = .ok (some 1, some 1) := rfl

example : (intern { profile with select? := fun _ => some 1 } index (some 2) 2).commit arena =
    (.error (.collision 1), arena) := by
  apply Mutable.Mutation.commit_error
  exact intern_rejects_conflict _ _ _ _ _ ⟨rfl, rfl⟩ rfl (by decide)

end Silmaril.Semantics.Arena.Cas.Intern.Examples
