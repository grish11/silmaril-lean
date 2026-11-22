module

public import Silmaril.Semantics.Arena.Cas.Intern.Defs
public import Silmaril.Semantics.Arena.Cas.Thms
public import Silmaril.Semantics.Naming.Admission.Thms

public section

namespace Silmaril.Proofs.Semantics.Arena.Cas.Intern

open Silmaril.Semantics
open Silmaril.Semantics.Arena.Cas
open Silmaril.Semantics.Arena.Cas.Intern

variable {Key Name Obj : Type} [DecidableEq Key] [DecidableEq Name]

theorem intern_spec {profile : Profile Name Obj} {index : Index Name Key} {fresh : Option Key}
    {obj : Obj} {arena updated : State Key Name Obj} {entry : Entry Key Name}
    (success : intern profile index fresh obj arena = .ok (entry, updated)) : Outcome profile index obj arena updated entry := by
  unfold intern at success
  split at success
  next bytes encoded =>
    split at success
    next name selected =>
      cases staged : Naming.admit arena.blocks [(name, bytes)] with
      | error collision => simp [staged, Bind.bind, Except.bind, Except.mapError] at success
      | ok blocks =>
        simp only [staged, Except.mapError, Bind.bind, Except.bind] at success
        split at success
        next key indexed =>
          split at success
          next linked existing present =>
            split at success
            next matched =>
              obtain ⟨equal, stored⟩ := matched
              subst name
              have same : (⟨key, linked⟩ : Entry Key Name) = entry ∧ arena = updated := by simpa using success
              obtain ⟨rfl, rfl⟩ := same
              exact ⟨bytes, ⟨encoded, selected⟩, Or.inl ⟨indexed, rfl, ⟨existing, present⟩, stored⟩⟩
            next => contradiction
          next => contradiction
        next indexed =>
          cases supplied : fresh with
          | none => simp [supplied] at success
          | some key =>
            cases present : arena.slots key with
            | none =>
              let after : State Key Name Obj := ⟨arena.slots.replaceAt key (some ⟨some name, some obj⟩), blocks⟩
              have same : (⟨key, name⟩ : Entry Key Name) = entry ∧ after = updated := by
                simpa [supplied, present, after] using success
              obtain ⟨rfl, rfl⟩ := same
              exact ⟨bytes, ⟨encoded, selected⟩, Or.inr ⟨indexed, present, rfl, Naming.admit_eq_union staged⟩⟩
            | some _ => simp [supplied, present] at success
    next => contradiction
  next => contradiction

omit [DecidableEq Name] in
theorem binding_and_valid {profile : Profile Name Obj} {index : Index Name Key} {obj : Obj}
    {arena updated : State Key Name Obj} {entry : Entry Key Name}
    (outcome : Outcome profile index obj arena updated entry) (valid : profile.Valid arena) :
    profile.Valid updated ∧ Naming.Subset (Naming.graph arena.blocks) (Naming.graph updated.blocks) ∧
      ∃ resident bytes, updated.slots entry.key = some ⟨some entry.name, some resident⟩ ∧
        profile.Certifies entry.name obj bytes ∧ profile.Certifies entry.name resident bytes ∧
        updated.blocks entry.name = some bytes := by
  obtain ⟨bytes, certified, reused | inserted⟩ := outcome
  · obtain ⟨_, rfl, ⟨resident, present⟩, stored⟩ := reused
    obtain ⟨other, check, readback⟩ := valid entry.key entry.name resident present
    rw [stored] at readback
    cases readback
    exact ⟨valid, fun _ _ old => old, resident, bytes, present, certified, check, stored⟩
  · obtain ⟨_, _, slots, graph⟩ := inserted
    have stored : updated.blocks entry.name = some bytes := by
      change Naming.graph updated.blocks _ _
      rw [graph]
      exact Or.inr (by simp [Naming.listed])
    have preserved : Naming.Subset (Naming.graph arena.blocks) (Naming.graph updated.blocks) := by
      rw [graph]
      exact fun _ _ old => Or.inl old
    refine ⟨?_, preserved, obj, bytes, by simp [slots, Arena.State.replaceAt], certified, certified, stored⟩
    intro key name resident present
    rw [slots] at present
    by_cases same : entry.key = key
    · simp [Arena.State.replaceAt, same] at present
      obtain ⟨rfl, rfl⟩ := present
      exact ⟨bytes, certified, stored⟩
    · simp [Arena.State.replaceAt, same] at present
      obtain ⟨old, checked, readback⟩ := valid key name resident present
      exact ⟨old, checked, preserved readback⟩

theorem index_after {profile : Profile Name Obj} {index : Index Name Key} {obj : Obj}
    {arena updated : State Key Name Obj} {entry : Entry Key Name}
    (exactBefore : index.Exact arena) (outcome : Outcome profile index obj arena updated entry) :
    (index.remember entry.name entry.key).Exact updated := by
  obtain ⟨_, _, reused | inserted⟩ := outcome
  · obtain ⟨indexed, rfl, _, _⟩ := reused
    intro name key
    by_cases same : name = entry.name
    · simpa [Index.remember, same, indexed] using exactBefore entry.name key
    · simpa [Index.remember, same] using exactBefore name key
  · obtain ⟨indexed, vacant, slots, _⟩ := inserted
    intro name key
    by_cases sameKey : entry.key = key
    · subst key
      change index.remember entry.name entry.key name = some entry.key ↔
        ∃ resident, updated.slots entry.key = some ⟨some name, some resident⟩
      rw [slots]
      by_cases sameName : name = entry.name
      · simp [Index.remember, Arena.State.replaceAt, sameName]
      · have absent : index name ≠ some entry.key := fun hit => by
          obtain ⟨resident, present⟩ := (exactBefore name entry.key).mp hit
          rw [vacant] at present
          contradiction
        simp [Index.remember, Arena.State.replaceAt, sameName, Ne.symm sameName, absent]
    · have unchanged : key ∈ updated.attachedKeys name ↔ key ∈ arena.attachedKeys name := by
        change (∃ resident, updated.slots key = some ⟨some name, some resident⟩) ↔
          ∃ resident, arena.slots key = some ⟨some name, some resident⟩
        simp [slots, Arena.State.replaceAt, sameKey]
      by_cases sameName : name = entry.name
      · subst name
        rw [unchanged, ← exactBefore, indexed]
        simp [Index.remember, sameKey]
      · simpa [Index.remember, sameName, unchanged] using exactBefore name key

theorem replace_shared_spec {profile : Profile Name Obj} {index : Index Name Key} {fresh : Option Key}
    {source : Key} {obj : Obj} {arena updated : State Key Name Obj} {entry : Entry Key Name}
    (success : replaceShared profile index fresh source obj arena = .ok (entry, updated)) :
    Outcome profile index obj arena updated entry ∧ ∀ key, (arena.slots key).isSome → updated.slots key = arena.slots key := by
  unfold replaceShared at success
  split at success
  next =>
    split at success
    next =>
      have outcome := intern_spec success
      refine ⟨outcome, ?_⟩
      obtain ⟨_, _, reused | inserted⟩ := outcome
      · rw [reused.2.1]
        exact fun _ _ => rfl
      · obtain ⟨_, vacant, slots, _⟩ := inserted
        intro key occupied
        have different : entry.key ≠ key := fun same => by simp [← same, vacant] at occupied
        simp [slots, Arena.State.replaceAt, different]
    next => contradiction
  next => contradiction

end Silmaril.Proofs.Semantics.Arena.Cas.Intern
