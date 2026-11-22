module

public import Silmaril.Semantics.Arena.Cas.Defs

@[expose] public section

namespace Silmaril.Semantics.Arena.Cas.Intern

variable {Key Name Obj : Type}

abbrev Index (Name Key : Type) := Name → Option Key

namespace Index

/-- Both directions matter: an index miss must rule out a resident alias.
Name-only reservations are deliberately outside this invariant. -/
def Exact (index : Index Name Key) (arena : State Key Name Obj) : Prop :=
  ∀ name key, index name = some key ↔ key ∈ arena.attachedKeys name

def remember [DecidableEq Name] (index : Index Name Key) (name : Name) (key : Key) : Index Name Key :=
  fun query => if query = name then some key else index query

end Index

inductive Fault (Name : Type) where
  | unencodable
  | unnamed
  | collision (name : Name)
  | staleHit
  | noCapacity
  | occupied
  | sourceVacant
  | sourceUnresident
  deriving DecidableEq, Repr

structure Entry (Key Name : Type) where
  key : Key
  name : Name
  deriving DecidableEq, Repr

/-- Publication is staged before reuse or allocation. Reusing a key checks an
actual resident name and exact resident bytes, not just digest equality. -/
def intern [DecidableEq Key] [DecidableEq Name] (profile : Profile Name Obj) (index : Index Name Key)
    (fresh : Option Key) (obj : Obj) : Mutable.Mutation (State Key Name Obj) (Fault Name) (Entry Key Name) :=
  fun arena => do
    let some bytes := profile.encode? obj | .error .unencodable
    let some name := profile.select? bytes | .error .unnamed
    let blocks ← (Naming.admit arena.blocks [(name, bytes)]).mapError Fault.collision
    match index name with
    | some key =>
      let some ⟨some linked, some _⟩ := arena.slots key | .error .staleHit
      if linked = name ∧ arena.blocks name = some bytes then .ok (⟨key, name⟩, arena) else .error .staleHit
    | none =>
      let some key := fresh | .error .noCapacity
      match arena.slots key with
      | none => .ok (⟨key, name⟩, ⟨arena.slots.replaceAt key (some ⟨some name, some obj⟩), blocks⟩)
      | some _ => .error .occupied

/-- This edit does not overwrite a shared source. The returned key is the
replacement; the caller decides whether to update one reference to it. -/
def replaceShared [DecidableEq Key] [DecidableEq Name] (profile : Profile Name Obj) (index : Index Name Key)
    (fresh : Option Key) (source : Key) (obj : Obj) : Mutable.Mutation (State Key Name Obj) (Fault Name) (Entry Key Name) :=
  fun arena => do
    let some slot := arena.slots source | .error .sourceVacant
    let some _ := slot.payload | .error .sourceUnresident
    intern profile index fresh obj arena

def Outcome [DecidableEq Key] (profile : Profile Name Obj) (index : Index Name Key)
    (obj : Obj) (arena updated : State Key Name Obj) (entry : Entry Key Name) : Prop :=
  ∃ bytes, profile.Certifies entry.name obj bytes ∧
    ((index entry.name = some entry.key ∧ updated = arena ∧ entry.key ∈ arena.attachedKeys entry.name ∧
        arena.blocks entry.name = some bytes) ∨
      (index entry.name = none ∧ arena.slots entry.key = none ∧
        updated.slots = arena.slots.replaceAt entry.key (some ⟨some entry.name, some obj⟩) ∧
        Naming.graph updated.blocks = Naming.union (Naming.graph arena.blocks) (Naming.listed [(entry.name, bytes)])))

end Silmaril.Semantics.Arena.Cas.Intern
