module

public import Silmaril.Semantics.Arena.Cas.Defs
import Silmaril.Proofs.Semantics.Arena.Cas

public section

namespace Silmaril.Semantics.Arena.Cas

variable {Key Name Obj : Type}

theorem State.attachedKeys_subset_claimKeys (arena : State Key Name Obj) (name : Name) :
    arena.attachedKeys name ⊆ arena.claimKeys name := by
  rintro key ⟨obj, attached⟩
  exact show arena.slots.keyName key = some name by simp [Arena.State.keyName, attached]

theorem State.plain_refines [DecidableEq Key] (arena : State Key Name Obj) (key : Key)
    (operation : Mutable.Change Obj) :
    (State.plain.change key operation arena).map (fun (_, next) => ((), next.slots)) =
      Mutable.Access.raw.change key operation arena.slots := by
  change ((Mutable.Access.raw.change key operation arena.slots).map _).map _ = _
  cases Mutable.Access.raw.change key operation arena.slots with
  | error => rfl
  | ok pair => obtain ⟨⟨⟩, _⟩ := pair; rfl

theorem State.plain_valid [DecidableEq Key] {profile : Profile Name Obj} {arena updated : State Key Name Obj}
    {key : Key} {operation : Mutable.Change Obj} (valid : profile.Valid arena)
    (accepted : State.plain.change key operation arena = .ok ((), updated)) :
    profile.Valid updated ∧ updated.blocks = arena.blocks :=
  Proofs.Semantics.Arena.Cas.plain_valid valid accepted

theorem Profile.validate_ok [DecidableEq Name] {profile : Profile Name Obj} {cell : Option (Slot Name Obj)}
    {name : Name} {obj : Obj} {bytes : ByteArray} : profile.validate cell name = .ok (obj, bytes) ↔
    cell.map Slot.payload = some (some obj) ∧ profile.Certifies name obj bytes :=
  Proofs.Semantics.Arena.Cas.validate_ok

theorem Profile.attach_spec [DecidableEq Key] [DecidableEq Name] {profile : Profile Name Obj}
    {arena updated : State Key Name Obj} {key : Key} {name : Name}
    (accepted : profile.attach key name arena = .ok ((), updated)) : profile.Attached arena updated key name :=
  Proofs.Semantics.Arena.Cas.attach_spec accepted

/-- A collision is with authoritative bytes, not merely with another arena key. -/
theorem Profile.attach_collision_iff [DecidableEq Key] [DecidableEq Name] (profile : Profile Name Obj)
    (arena : State Key Name Obj) (key : Key) (name : Name) :
    profile.attach key name arena = .error (.collision name) ↔
      (∃ obj bytes previous, (arena.slots key).map Slot.payload = some (some obj) ∧
        profile.Certifies name obj bytes ∧ arena.blocks name = some previous ∧ previous ≠ bytes) :=
  Proofs.Semantics.Arena.Cas.attach_collision_iff profile arena key name

theorem Profile.Attached.valid [DecidableEq Key] {profile : Profile Name Obj} {arena updated : State Key Name Obj}
    {key : Key} {name : Name} (attached : profile.Attached arena updated key name) (valid : profile.Valid arena) :
    profile.Valid updated :=
  Proofs.Semantics.Arena.Cas.attached_valid valid attached

theorem Profile.Attached.readback [DecidableEq Key] {profile : Profile Name Obj} {arena updated : State Key Name Obj}
    {key : Key} {name : Name} (attached : profile.Attached arena updated key name) :
    ∃ obj bytes, updated.slots key = some ⟨some name, some obj⟩ ∧ profile.Certifies name obj bytes ∧
      updated.blocks name = some bytes :=
  Proofs.Semantics.Arena.Cas.attached_readback attached

theorem Profile.Valid.alias_bytes {profile : Profile Name Obj} {arena : State Key Name Obj}
    {first second : Key} {name : Name} {left right : Obj} (valid : profile.Valid arena)
    (one : arena.slots first = some ⟨some name, some left⟩) (two : arena.slots second = some ⟨some name, some right⟩) :
    ∃ bytes, profile.Certifies name left bytes ∧ profile.Certifies name right bytes :=
  Proofs.Semantics.Arena.Cas.alias_bytes valid one two

end Silmaril.Semantics.Arena.Cas
