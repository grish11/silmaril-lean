module

import Silmaril.Semantics.Arena.Cas.Thms
import Silmaril.Semantics.Arena.Mutable.Thms

namespace Silmaril.Semantics.Arena.Cas.Examples

private def block (obj : UInt8) : ByteArray := ⟨#[obj]⟩

private def constantProfile : Profile Nat UInt8 := ⟨some ∘ block, fun _ => some 7⟩

private def cells : State Nat Nat UInt8 where
  slots
  | 0 | 1 => some ⟨some 7, some 1⟩
  | 2 => some ⟨some 7, none⟩
  | 3 => some ⟨none, some 2⟩
  | _ => none
  blocks name := if name = 7 then some (block 1) else none

example : 0 ∈ cells.attachedKeys 7 ∧ 1 ∈ cells.attachedKeys 7 ∧
    2 ∈ cells.claimKeys 7 ∧ 2 ∉ cells.attachedKeys 7 := by
  refine ⟨⟨1, rfl⟩, ⟨1, rfl⟩, rfl, ?_⟩
  rintro ⟨obj, impossible⟩
  cases impossible

example : constantProfile.attach 2 7 cells = .error .unresident := rfl
example : constantProfile.attach 4 7 cells = .error .vacant := rfl
example : constantProfile.attach 3 8 cells = .error (.mismatch 7) := rfl

example : ({ constantProfile with encode? := fun _ => none }).attach 3 7 cells = .error .unencodable := rfl
example : ({ constantProfile with select? := fun _ => none }).attach 3 7 cells = .error .unnamed := rfl

example : (constantProfile.attach 3 7).commit cells = (.error (.collision 7), cells) := by
  apply Mutable.Mutation.commit_error
  exact (constantProfile.attach_collision_iff cells 3 7).mpr
    ⟨2, block 2, block 1, rfl, ⟨rfl, rfl⟩, rfl, by decide⟩

example : (State.plain.change 0 (.replace 2) cells).map
    (fun (_, updated) => (updated.slots.keyName 0, updated.slots.keyName 1, updated.blocks 7)) =
    .ok (none, some 7, some (block 1)) := rfl

example : (constantProfile.attach 3 7 { cells with blocks := fun _ => none }).map
    (fun (_, updated) => (updated.slots.keyName 3, updated.blocks 7)) = .ok (some 7, some (block 2)) := rfl

end Silmaril.Semantics.Arena.Cas.Examples
