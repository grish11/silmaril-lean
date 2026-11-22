module

public import Silmaril.Semantics.Arena.Mutable.Defs
public import Silmaril.Semantics.Naming.Admission.Defs

@[expose] public section

namespace Silmaril.Semantics.Arena.Cas

variable {Key Name Obj : Type}

/-- Separate the editable handle table from the authoritative naming snapshot.
`none` in `blocks` must mean absent, not an unavailable cache read. -/
structure State (Key Name Obj : Type) where
  slots : Arena.State Key Name Obj
  blocks : Name → Option ByteArray

structure Profile (Name Obj : Type) where
  encode? : Obj → Option ByteArray
  select? : ByteArray → Option Name

inductive Fault (Name : Type) where
  | vacant
  | unresident
  | unencodable
  | unnamed
  | mismatch (selected : Name)
  | collision (name : Name)
  deriving DecidableEq, Repr

namespace State

/-- Names of reservations are claims. They can outnumber admitted resident
keys and do not by themselves imply any binding in the byte snapshot. -/
def claimKeys (arena : State Key Name Obj) (name : Name) : Set Key :=
  {key | arena.slots.keyName key = some name}

/-- The default reverse lookup returns every co-present key. For valid states
these are verified resident attachments; this need not be a singleton. -/
def attachedKeys (arena : State Key Name Obj) (name : Name) : Set Key :=
  {key | ∃ obj, arena.slots key = some ⟨some name, some obj⟩}

def change [DecidableEq Key] (key : Key) (operation : Mutable.Change Obj) :
    Mutable.Mutation (State Key Name Obj) Arena.Fault Unit := fun arena =>
  (Mutable.Access.raw.change key operation arena.slots).map fun (_, slots) => ((), {arena with slots})

/-- Plain replacement uses a stable key but drops the local name. The byte
snapshot is persistent across all plain edits, including remove. -/
def plain [DecidableEq Key] : Mutable.Access (State Key Name Obj) Key Obj Arena.Fault where
  read arena := Mutable.Access.raw.read arena.slots
  change := change

end State

namespace Profile

def Certifies (profile : Profile Name Obj) (name : Name) (obj : Obj) (bytes : ByteArray) : Prop :=
  profile.encode? obj = some bytes ∧ profile.select? bytes = some name

/-- The profile checks witnessed attachments, not reservations, anonymous
residents, or unrelated blocks already in the reference snapshot. -/
def Valid (profile : Profile Name Obj) (arena : State Key Name Obj) : Prop :=
  ∀ key name obj, arena.slots key = some ⟨some name, some obj⟩ →
    ∃ bytes, profile.Certifies name obj bytes ∧ arena.blocks name = some bytes

def validate [DecidableEq Name] (profile : Profile Name Obj) (cell : Option (Slot Name Obj)) (name : Name) :
    Except (Fault Name) (Obj × ByteArray) := do
  let some slot := cell | .error .vacant
  let some obj := slot.payload | .error .unresident
  let some bytes := profile.encode? obj | .error .unencodable
  let some selected := profile.select? bytes | .error .unnamed
  if selected = name then .ok (obj, bytes) else .error (.mismatch selected)

/-- Verify the caller's claimed name, then admit its exact bytes, and attach
only after admission succeeds. The oracle's `none` never certifies a name. -/
def attach [DecidableEq Key] [DecidableEq Name] (profile : Profile Name Obj) (key : Key) (name : Name) :
    Mutable.Mutation (State Key Name Obj) (Fault Name) Unit := fun arena => do
  let (obj, bytes) ← profile.validate (arena.slots key) name
  let blocks ← (Naming.admit arena.blocks [(name, bytes)]).mapError Fault.collision
  return ((), ⟨arena.slots.replaceAt key (some ⟨some name, some obj⟩), blocks⟩)

def Attached [DecidableEq Key] (profile : Profile Name Obj) (before after : State Key Name Obj)
    (key : Key) (name : Name) : Prop :=
  ∃ obj bytes, (before.slots key).map Slot.payload = some (some obj) ∧
    profile.Certifies name obj bytes ∧ after.slots = before.slots.replaceAt key (some ⟨some name, some obj⟩) ∧
      Naming.graph after.blocks = Naming.union (Naming.graph before.blocks) (Naming.listed [(name, bytes)])

end Profile

end Silmaril.Semantics.Arena.Cas
