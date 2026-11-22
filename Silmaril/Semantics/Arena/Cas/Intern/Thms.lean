module

public import Silmaril.Semantics.Arena.Cas.Intern.Defs
import Silmaril.Proofs.Semantics.Arena.Cas.Intern

public section

namespace Silmaril.Semantics.Arena.Cas.Intern

variable {Key Name Obj : Type}

theorem Index.Exact.unique {arena : State Key Name Obj} {index : Index Name Key} (exactIndex : index.Exact arena)
    {name : Name} {left right : Key} (first : left ∈ arena.attachedKeys name) (second : right ∈ arena.attachedKeys name) :
    left = right := Option.some.inj (((exactIndex name left).mpr first).symm.trans ((exactIndex name right).mpr second))

theorem intern_spec [DecidableEq Key] [DecidableEq Name] {profile : Profile Name Obj} {index : Index Name Key}
    {fresh : Option Key} {obj : Obj} {arena updated : State Key Name Obj} {entry : Entry Key Name}
    (success : intern profile index fresh obj arena = .ok (entry, updated)) : Outcome profile index obj arena updated entry :=
  Proofs.Semantics.Arena.Cas.Intern.intern_spec success

theorem intern_rejects_conflict [DecidableEq Key] [DecidableEq Name] (profile : Profile Name Obj) (index : Index Name Key)
    (fresh : Option Key) (obj : Obj) (arena : State Key Name Obj) {name : Name} {bytes previous : ByteArray}
    (certified : profile.Certifies name obj bytes) (present : arena.blocks name = some previous) (different : previous ≠ bytes) :
    intern profile index fresh obj arena = .error (.collision name) := by
  obtain ⟨encoded, selected⟩ := certified
  simp [intern, encoded, selected, Naming.admit, Naming.admitOne, present, different, Bind.bind, Except.bind, Except.mapError]

/-- Success refines the requested object at its serialized observation. With
a recovering encoder, the two source objects also agree. -/
theorem Outcome.valid [DecidableEq Key] {profile : Profile Name Obj} {index : Index Name Key} {obj : Obj}
    {arena updated : State Key Name Obj} {entry : Entry Key Name}
    (outcome : Outcome profile index obj arena updated entry) (valid : profile.Valid arena) :
    profile.Valid updated ∧ Naming.Subset (Naming.graph arena.blocks) (Naming.graph updated.blocks) ∧
      ∃ resident bytes, updated.slots entry.key = some ⟨some entry.name, some resident⟩ ∧
        profile.Certifies entry.name obj bytes ∧ profile.Certifies entry.name resident bytes ∧
        updated.blocks entry.name = some bytes :=
  Proofs.Semantics.Arena.Cas.Intern.binding_and_valid outcome valid

theorem Outcome.index_after [DecidableEq Key] [DecidableEq Name] {profile : Profile Name Obj} {index : Index Name Key}
    {obj : Obj} {arena updated : State Key Name Obj} {entry : Entry Key Name}
    (outcome : Outcome profile index obj arena updated entry) (exactBefore : index.Exact arena) :
    (index.remember entry.name entry.key).Exact updated :=
  Proofs.Semantics.Arena.Cas.Intern.index_after exactBefore outcome

/-- For an index hit, the returned key is exactly the existing key and no
state changes. This includes replacing a shared object with the same name
and bytes when the source is the exact index hit. -/
theorem Outcome.reused [DecidableEq Key] {profile : Profile Name Obj} {index : Index Name Key} {obj : Obj}
    {arena updated : State Key Name Obj} {entry : Entry Key Name} {existing : Key}
    (outcome : Outcome profile index obj arena updated entry) (hit : index entry.name = some existing) :
    entry.key = existing ∧ updated = arena := by
  obtain ⟨_, _, ⟨indexed, unchanged, _, _⟩ | ⟨unindexed, _, _, _⟩⟩ := outcome
  · exact ⟨Option.some.inj (indexed.symm.trans hit), unchanged⟩
  · rw [hit] at unindexed; contradiction

theorem replace_shared_spec [DecidableEq Key] [DecidableEq Name] {profile : Profile Name Obj} {index : Index Name Key}
    {fresh : Option Key} {source : Key} {obj : Obj} {arena updated : State Key Name Obj} {entry : Entry Key Name}
    (success : replaceShared profile index fresh source obj arena = .ok (entry, updated)) :
    Outcome profile index obj arena updated entry ∧ ∀ key, (arena.slots key).isSome → updated.slots key = arena.slots key :=
  Proofs.Semantics.Arena.Cas.Intern.replace_shared_spec success

end Silmaril.Semantics.Arena.Cas.Intern
