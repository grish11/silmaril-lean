module

public import Silmaril.Semantics.Arena.Cas.Defs
public import Silmaril.Semantics.Arena.Mutable.Thms
public import Silmaril.Semantics.Naming.Admission.Thms

public section

namespace Silmaril.Proofs.Semantics.Arena.Cas

open Silmaril.Semantics.Arena (Slot)
open Silmaril.Semantics.Arena.Cas
open Silmaril.Semantics

variable {Key Name Obj : Type} [DecidableEq Key] [DecidableEq Name]

theorem validate_ok {profile : Profile Name Obj} {cell : Option (Slot Name Obj)} {name : Name}
    {obj : Obj} {bytes : ByteArray} : profile.validate cell name = .ok (obj, bytes) ↔
    cell.map Slot.payload = some (some obj) ∧ profile.Certifies name obj bytes := by
  constructor
  · intro accepted
    unfold Profile.validate at accepted
    split at accepted <;> try contradiction
    split at accepted <;> try contradiction
    split at accepted <;> try contradiction
    split at accepted <;> try contradiction
    split at accepted <;> simp_all [Profile.Certifies]
  · rintro ⟨observed, encoded, selected⟩
    cases cell with
    | none => contradiction
    | some slot =>
      simp at observed
      simp [Profile.validate, observed, encoded, selected]

theorem attach_spec {profile : Profile Name Obj} {arena updated : State Key Name Obj} {key : Key} {name : Name}
    (accepted : profile.attach key name arena = .ok ((), updated)) : profile.Attached arena updated key name := by
  cases result : profile.validate (arena.slots key) name with
  | error fault => simp [Profile.attach, Bind.bind, Except.bind, result] at accepted
  | ok pair =>
    obtain ⟨obj, bytes⟩ := pair
    obtain ⟨observed, certified⟩ := validate_ok.mp result
    cases admitted : Naming.admit arena.blocks [(name, bytes)] with
    | error collision => simp [Profile.attach, Bind.bind, Except.bind, result, admitted, Except.mapError] at accepted
    | ok blocks =>
      have exactState : (⟨arena.slots.replaceAt key (some ⟨some name, some obj⟩), blocks⟩ : State Key Name Obj) = updated := by
        simpa [Profile.attach, Bind.bind, Except.bind, result, admitted, Except.mapError, Pure.pure, Except.pure] using accepted
      subst updated
      exact ⟨obj, bytes, observed, certified, rfl, Naming.admit_eq_union admitted⟩

theorem attach_collision_iff (profile : Profile Name Obj) (arena : State Key Name Obj) (key : Key) (name : Name) :
    profile.attach key name arena = .error (.collision name) ↔
      (∃ obj bytes previous, (arena.slots key).map Slot.payload = some (some obj) ∧
        profile.Certifies name obj bytes ∧ arena.blocks name = some previous ∧ previous ≠ bytes) := by
  cases prepared : profile.validate (arena.slots key) name with
  | error fault =>
    have notCollision : fault ≠ .collision name := by
      intro equal
      subst fault
      have impossible := prepared
      unfold Profile.validate at impossible
      split at impossible
      split at impossible
      split at impossible
      split at impossible
      split at impossible
      all_goals simp at impossible
    have noCandidate : ¬ (∃ obj bytes previous, (arena.slots key).map Slot.payload = some (some obj) ∧
        profile.Certifies name obj bytes ∧ arena.blocks name = some previous ∧ previous ≠ bytes) := by
      rintro ⟨obj, bytes, _, seen, certified, _, _⟩
      have also := (validate_ok (profile := profile)).mpr ⟨seen, certified⟩
      rw [prepared] at also
      contradiction
    exact iff_of_false (by simpa [Profile.attach, Bind.bind, Except.bind, prepared] using notCollision) noCandidate
  | ok pair =>
    obtain ⟨obj, bytes⟩ := pair
    obtain ⟨observed, certified⟩ := validate_ok.mp prepared
    have rhs : (∃ other data previous, (arena.slots key).map Slot.payload = some (some other) ∧
        profile.Certifies name other data ∧ arena.blocks name = some previous ∧ previous ≠ data) ↔
        ∃ previous, arena.blocks name = some previous ∧ previous ≠ bytes := by
      refine ⟨?_, fun ⟨previous, present, different⟩ => ⟨obj, bytes, previous, observed, certified, present, different⟩⟩
      rintro ⟨other, data, previous, seen, accepted, present, different⟩
      have eq : (obj, bytes) = (other, data) := Except.ok.inj (prepared.symm.trans (validate_ok.mpr ⟨seen, accepted⟩))
      have sameBytes : bytes = data := congrArg Prod.snd eq
      exact ⟨previous, present, sameBytes.symm ▸ different⟩
    rw [rhs]
    cases present : arena.blocks name with
    | none => simp [Profile.attach, prepared, Naming.admit, Naming.admitOne, present, Except.mapError, Bind.bind,
        Except.bind, Pure.pure, Except.pure]
    | some previous =>
      by_cases same : previous = bytes <;>
        simp [Profile.attach, prepared, Naming.admit, Naming.admitOne, present, same, Except.mapError, Bind.bind,
          Except.bind, Pure.pure, Except.pure]

omit [DecidableEq Name] in
theorem attached_valid {profile : Profile Name Obj} {arena updated : State Key Name Obj} {key : Key} {name : Name}
    (valid : profile.Valid arena) (attached : profile.Attached arena updated key name) : profile.Valid updated := by
  obtain ⟨obj, bytes, _, certified, slots, blocks⟩ := attached
  intro query other value resident
  rw [slots] at resident
  by_cases same : key = query
  · simp [Arena.State.replaceAt, same] at resident
    obtain ⟨rfl, rfl⟩ := resident
    refine ⟨bytes, certified, ?_⟩
    change Naming.graph updated.blocks _ _
    rw [blocks]
    exact Or.inr (by simp [Naming.listed])
  · simp [Arena.State.replaceAt, same] at resident
    obtain ⟨old, check, stored⟩ := valid query other value resident
    refine ⟨old, check, ?_⟩
    change Naming.graph updated.blocks _ _
    rw [blocks]
    exact Or.inl stored

omit [DecidableEq Name] in
theorem attached_readback {profile : Profile Name Obj} {arena updated : State Key Name Obj} {key : Key} {name : Name}
    (attached : profile.Attached arena updated key name) :
    ∃ obj bytes, updated.slots key = some ⟨some name, some obj⟩ ∧ profile.Certifies name obj bytes ∧
      updated.blocks name = some bytes := by
  obtain ⟨obj, bytes, _, certified, slots, blocks⟩ := attached
  refine ⟨obj, bytes, by simp [slots, Arena.State.replaceAt], certified, ?_⟩
  change Naming.graph updated.blocks name bytes
  rw [blocks]
  exact Or.inr (by simp [Naming.listed])

omit [DecidableEq Key] [DecidableEq Name] in
theorem alias_bytes {profile : Profile Name Obj} {arena : State Key Name Obj} {first second : Key} {name : Name}
    {left right : Obj} (valid : profile.Valid arena) (one : arena.slots first = some ⟨some name, some left⟩)
    (two : arena.slots second = some ⟨some name, some right⟩) :
    ∃ bytes, profile.Certifies name left bytes ∧ profile.Certifies name right bytes := by
  obtain ⟨leftBytes, leftCert, leftBlock⟩ := valid first name left one
  obtain ⟨rightBytes, rightCert, rightBlock⟩ := valid second name right two
  rw [leftBlock] at rightBlock
  cases rightBlock
  exact ⟨leftBytes, leftCert, rightCert⟩

omit [DecidableEq Name] in
theorem plain_valid {profile : Profile Name Obj} {arena updated : State Key Name Obj} {key : Key}
    {operation : Arena.Mutable.Change Obj} (valid : profile.Valid arena)
    (accepted : State.plain.change key operation arena = .ok ((), updated)) :
    profile.Valid updated ∧ updated.blocks = arena.blocks := by
  cases stepped : Arena.Mutable.Access.raw.change key operation arena.slots with
  | error fault => simp [State.plain, State.change, stepped, Except.map] at accepted
  | ok pair =>
    obtain ⟨⟨⟩, slots⟩ := pair
    have eq : { arena with slots } = updated := by simpa [State.plain, State.change, stepped, Except.map] using accepted
    subst updated
    obtain ⟨localSpec, frame⟩ := Arena.Mutable.Access.raw_spec stepped
    refine ⟨?_, rfl⟩
    intro query other value resident
    by_cases same : key = query
    · subst query
      change slots key = _ at resident
      rw [resident] at localSpec
      cases operation <;> cases occupancy : arena.slots key <;>
        simp [Arena.Mutable.Change.apply, Arena.Edit.apply, Except.map, occupancy] at localSpec
    · change slots query = _ at resident
      rw [frame query same] at resident
      exact valid query other value resident

end Silmaril.Proofs.Semantics.Arena.Cas
