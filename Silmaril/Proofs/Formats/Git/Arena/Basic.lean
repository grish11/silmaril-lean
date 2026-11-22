module

public import Silmaril.Formats.Git.Arena.Defs

public section

namespace Silmaril.Proofs.Formats.Git.Arena

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena
open Silmaril.Semantics

variable {Name Payload : Type} {limit : Nat}
variable [DecidableEq Name] [DecidableEq Payload]
variable {profile : Profile Name Payload} {arena after : State limit Name Payload} {key : Fin limit}
variable {id : Silmaril.Formats.Git.Arena.Id Name} {payload : Payload}

theorem step_spec {edit : Edit Name Payload} :
    arena.step profile key edit = .ok after ↔
    ∃ cell, edit.apply (arena key) = .ok cell ∧ after key = some cell ∧ cell.Valid profile ∧
      after.Coherent profile ∧ ∀ query, key ≠ query → after query = arena query := by
  constructor
  · intro stepped
    cases edited : edit.apply (arena key) with
    | error fault => simp [State.step, edited] at stepped
    | ok cell =>
      by_cases valid : cell.Valid profile
      · by_cases coherent : State.Coherent profile (Semantics.Arena.State.replaceAt arena key (some cell))
        · have next : Semantics.Arena.State.replaceAt arena key (some cell) = after := by
            simpa [State.step, edited, valid, coherent] using stepped
          subst after
          exact ⟨cell, rfl, by simp [Semantics.Arena.State.replaceAt], valid, coherent,
            fun query different => by simp [Semantics.Arena.State.replaceAt, different]⟩
        · simp [State.step, edited, valid, coherent] at stepped
      · simp [State.step, edited, valid] at stepped
  · rintro ⟨cell, edited, atKey, valid, coherent, frame⟩
    have next : Semantics.Arena.State.replaceAt arena key (some cell) = after := by
      funext query
      by_cases same : key = query
      · subst query
        simpa [Semantics.Arena.State.replaceAt] using atKey.symm
      · simp [Semantics.Arena.State.replaceAt, same, frame query same]
    simp [State.step, edited, valid, next, coherent]

theorem valid_step {edit : Edit Name Payload} (prior : arena.Valid profile)
    (stepped : arena.step profile key edit = .ok after) : after.Valid profile := by
  obtain ⟨cell, _, atKey, valid, coherent, frame⟩ := step_spec.mp stepped
  refine ⟨?_, coherent⟩
  intro query result present
  by_cases same : key = query
  · subst query
    simp [atKey] at present
    exact present ▸ valid
  · exact prior.1 query result (frame query same ▸ present)

omit [DecidableEq Payload] in theorem empty_valid (profile : Profile Name Payload) :
    State.Valid (limit := limit) profile Semantics.Arena.State.empty := by
  simp [State.Valid, State.Coherent, Semantics.Arena.State.empty]

theorem edit_extends {edit : Edit Name Payload} {old next : Cell Name Payload}
    (edited : edit.apply (some old) = .ok next) : old.Extends next := by
  cases edit with
  | insert | reserve => simp [Edit.apply] at edited
  | attach id kind =>
    by_cases compatible : Compatible old.claims.kind kind
    · simp [Edit.apply, compatible] at edited
      subst next
      refine ⟨?_, fun _ hit => hit, ?_⟩
      · intro name hit
        change name ∈ if _ then _ else _
        split <;> simp [hit]
      · intro previous hit
        change old.claims.kind.or kind = some previous
        change old.claims.kind = some previous at hit
        simp [hit]
    · simp [Edit.apply, compatible] at edited
  | materialize payload =>
    by_cases compatible : Compatible old.payload (some payload)
    · simp [Edit.apply, compatible] at edited
      subst next
      exact ⟨fun _ hit => hit, fun _ hit => (compatible _ hit _ rfl).symm ▸ rfl, fun _ hit => hit⟩
    · simp [Edit.apply, compatible] at edited

theorem step_extends {edit : Edit Name Payload} (stepped : arena.step profile key edit = .ok after) :
    arena.Extends after := by
  obtain ⟨cell, edited, atKey, _, _, frame⟩ := step_spec.mp stepped
  intro query old present
  by_cases same : key = query
  · subst query
    exact ⟨cell, atKey, edit_extends (present ▸ edited)⟩
  · exact ⟨old, (frame query same).symm ▸ present, fun _ hit => hit, fun _ hit => hit, fun _ hit => hit⟩

omit [DecidableEq Name] [DecidableEq Payload] in
theorem extends_observed (extended : arena.Extends after) : Naming.Subset arena.observed after.observed := by
  rintro name payload ⟨key, old, present, named, resident⟩
  obtain ⟨next, hit, refined⟩ := extended key old present
  exact ⟨key, next, hit, refined.1 named, refined.2.1 _ resident⟩

omit [DecidableEq Payload] in
theorem coherent_binding (coherent : arena.Coherent profile) : Naming.Binding arena.observed := by
  rintro name payload other ⟨left, first, here, named, resident⟩ ⟨right, second, there, sameName, value⟩
  exact (coherent left right first here second there ⟨name, named, sameName⟩).1 _ resident _ value

omit [DecidableEq Payload] in
theorem observed_accepted (valid : arena.Valid profile) (seen : arena.observed id payload) :
    profile.accepts id payload = true := by
  obtain ⟨key, cell, hit, named, resident⟩ := seen
  exact (valid.1 key cell hit payload resident).2 id named

omit [DecidableEq Payload] in
theorem accepted_provenance (accepted : profile.accepts id payload = true) :
    profile.derive id.lane payload = some id ∨
      (profile.derive id.lane payload = none ∧ profile.attest id payload = true) := by
  cases derived : profile.derive id.lane payload <;> simp_all [Profile.accepts]

omit [DecidableEq Payload] in
theorem mem_candidates {cell : Cell Name Payload} :
    cell ∈ arena.candidates id ↔ ∃ key : Fin limit, arena key = some cell ∧ id ∈ cell.claims.ids := by
  simp [State.candidates, Option.filter_eq_some_iff]

omit [DecidableEq Payload] in
theorem mem_payloads : payload ∈ (arena.candidates id).filterMap Semantics.Arena.Slot.payload ↔
    arena.observed id payload := by
  constructor
  · intro present
    obtain ⟨cell, candidate, hit⟩ := List.mem_filterMap.mp present
    obtain ⟨key, here, named⟩ := mem_candidates.mp candidate
    exact ⟨key, cell, here, named, hit⟩
  · rintro ⟨key, cell, hit, named, resident⟩
    exact List.mem_filterMap.mpr ⟨cell, mem_candidates.mpr ⟨key, hit, named⟩, resident⟩

theorem lookup_found_observed {expect : Option Kind} (found : arena.lookup profile id expect = .found payload) :
    arena.observed id payload := by
  apply mem_payloads.mp
  unfold State.lookup at found
  dsimp only at found
  split at found
  · contradiction
  split at found
  · contradiction
  split at found
  · contradiction
  split at found
  · contradiction
  · rename_i value rest values
    split at found
    · contradiction
    · cases found
      rw [values]
      simp

theorem lookup_found_of_observed (coherent : arena.Coherent profile) (seen : arena.observed id payload) :
    arena.lookup profile id = .found payload := by
  have present := mem_payloads.mpr seen
  have nonempty : (arena.candidates id).isEmpty = false := by
    cases candidates : arena.candidates id with
    | nil => simp [candidates] at present
    | cons => rfl
  have agreement : ¬ ∃ first ∈ arena.candidates id, ∃ second ∈ arena.candidates id,
      ¬ Cell.Agrees profile first second := by
    rintro ⟨first, candidate, second, other, different⟩
    obtain ⟨left, here, named⟩ := mem_candidates.mp candidate
    obtain ⟨right, there, nameAgain⟩ := mem_candidates.mp other
    exact different (coherent left right first here second there ⟨id, named, nameAgain⟩)
  have kindOK : ¬ ∃ cell ∈ arena.candidates id, ¬ Compatible none (Cell.kind profile cell) := by
    simp [Compatible]
  simp only [State.lookup, nonempty, Bool.false_eq_true, ite_false, agreement, kindOK]
  cases values : (arena.candidates id).filterMap Semantics.Arena.Slot.payload with
  | nil => simp [values] at present
  | cons value rest =>
    have valueSeen : arena.observed id value := mem_payloads.mp (by simp [values])
    simp [coherent_binding coherent valueSeen seen]

theorem assign_spec {lane : Lane} (assigned : arena.assign profile key lane = .ok (id, after)) :
    ∃ cell payload, arena key = some cell ∧ cell.payload = some payload ∧ profile.derive lane payload = some id ∧
      arena.step profile key (.attach id none) = .ok after := by
  cases here : arena key with
  | none => simp [State.assign, here, throw] at assigned
  | some cell =>
    cases resident : cell.payload with
    | none => simp [State.assign, here, resident, throw] at assigned
    | some payload =>
      cases derived : profile.derive lane payload with
      | none => simp [State.assign, here, resident, derived, throw] at assigned
      | some chosen =>
        cases stepped : arena.step profile key (.attach chosen none) with
        | error fault => simp [State.assign, here, resident, derived, stepped, Bind.bind, Except.bind] at assigned
        | ok next =>
          simp [State.assign, here, resident, derived, stepped, Bind.bind, Except.bind, Pure.pure, Except.pure] at assigned
          obtain ⟨rfl, rfl⟩ := assigned
          exact ⟨cell, payload, rfl, resident, derived, stepped⟩

theorem reserve_spec (kind : Option Kind) (reserved : arena.step profile key (.reserve id kind) = .ok after) :
    arena key = none ∧ after key = some ⟨some ⟨[id], kind⟩, none⟩ := by
  obtain ⟨cell, edited, atKey, _, _, _⟩ := step_spec.mp reserved
  cases here : arena key with
  | none =>
    simp [here, Edit.apply] at edited
    exact ⟨rfl, edited ▸ atKey⟩
  | some old => simp [here, Edit.apply] at edited

theorem insert_spec (inserted : arena.step profile key (.insert payload) = .ok after) :
    arena key = none ∧ after key = some ⟨none, some payload⟩ := by
  obtain ⟨cell, edited, atKey, _, _, _⟩ := step_spec.mp inserted
  cases here : arena key with
  | none =>
    simp [here, Edit.apply] at edited
    exact ⟨rfl, edited ▸ atKey⟩
  | some old => simp [here, Edit.apply] at edited

theorem materialize_spec {old : Cell Name Payload} (here : arena key = some old)
    (filled : arena.step profile key (.materialize payload) = .ok after) :
    after key = some { old with payload := some payload } := by
  obtain ⟨cell, edited, atKey, _, _, _⟩ := step_spec.mp filled
  by_cases compatible : Compatible old.payload (some payload)
  · simp [here, Edit.apply, compatible] at edited
    exact edited ▸ atKey
  · simp [here, Edit.apply, compatible] at edited

theorem attach_spec {old : Cell Name Payload} (here : arena key = some old) {kind : Option Kind}
    (attached : arena.step profile key (.attach id kind) = .ok after) :
    after key = some { old with name := some (old.claims.attach id kind) } := by
  obtain ⟨cell, edited, atKey, _, _, _⟩ := step_spec.mp attached
  by_cases compatible : Compatible old.claims.kind kind
  · simp [here, Edit.apply, compatible] at edited
    exact edited ▸ atKey
  · simp [here, Edit.apply, compatible] at edited

theorem insert_attach_commutes {reserved inserted attached : State limit Name Payload} (kind : Option Kind)
    (reserve : arena.step profile key (.reserve id kind) = .ok reserved)
    (fill : reserved.step profile key (.materialize payload) = .ok after)
    (insert : arena.step profile key (.insert payload) = .ok inserted)
    (attach : inserted.step profile key (.attach id kind) = .ok attached) : after = attached := by
  funext query
  by_cases same : key = query
  · subst query
    rw [materialize_spec (reserve_spec kind reserve).2 fill, attach_spec (insert_spec insert).2 attach]
    simp [Cell.claims, Claims.attach]
  · rw [(step_spec.mp fill).choose_spec.2.2.2.2 query same,
      (step_spec.mp reserve).choose_spec.2.2.2.2 query same,
      (step_spec.mp attach).choose_spec.2.2.2.2 query same,
      (step_spec.mp insert).choose_spec.2.2.2.2 query same]

theorem cache_spec {read : Reader Name Payload} (cached : arena.cache profile key id read = .ok (payload, after)) :
    ∃ cell, arena key = some cell ∧ id ∈ (Cell.claims cell).ids ∧
      ((cell.payload = some payload ∧ after = arena) ∨
       (cell.payload = none ∧ read id = .found payload ∧
         arena.step profile key (.materialize payload) = .ok after)) := by
  cases here : arena key with
  | none => simp [State.cache, here, throw] at cached
  | some cell =>
    by_cases claimed : id ∈ (Cell.claims cell).ids
    · cases resident : cell.payload with
      | none =>
        cases fetched : read id <;>
          simp [State.cache, here, claimed, resident, fetched, throw] at cached
        rename_i value
        cases stepped : arena.step profile key (.materialize value) <;>
          simp [stepped] at cached
        obtain ⟨rfl, rfl⟩ := cached
        exact ⟨cell, rfl, claimed, .inr ⟨resident, rfl, stepped⟩⟩
      | some value =>
        simp [State.cache, here, claimed, resident, Pure.pure, Except.pure] at cached
        obtain ⟨rfl, rfl⟩ := cached
        exact ⟨cell, rfl, claimed, .inl ⟨resident, rfl⟩⟩
    · simp [State.cache, here, claimed, throw, throwThe, Bind.bind, Except.bind] at cached

theorem cache_valid_observed {read : Reader Name Payload} (valid : arena.Valid profile)
    (cached : arena.cache profile key id read = .ok (payload, after)) :
    after.Valid profile ∧ arena.Extends after ∧ after.observed id payload := by
  obtain ⟨cell, here, claimed, resident | fetched⟩ := cache_spec cached
  · obtain ⟨present, rfl⟩ := resident
    exact ⟨valid, fun _ value hit =>
      ⟨value, hit, fun _ member => member, fun _ member => member, fun _ member => member⟩,
      key, cell, here, claimed, present⟩
  · obtain ⟨_, _, stepped⟩ := fetched
    exact ⟨valid_step valid stepped, step_extends stepped, key, { cell with payload := some payload },
      materialize_spec here stepped, claimed, rfl⟩

theorem readWire_found {expect : Option Kind} {bytes : ByteArray}
    (found : arena.readWire profile id expect = .found bytes) :
    ∃ payload, arena.observed id payload ∧ profile.wire id payload = some bytes := by
  cases selected : arena.lookup profile id expect <;> simp [State.readWire, selected, Read.andThen] at found
  rename_i value
  cases wire : profile.wire id value <;> simp [wire, Read.ofOption] at found
  exact ⟨value, lookup_found_observed selected, found ▸ wire⟩

omit [DecidableEq Payload] in
theorem observed_refines (valid : arena.Valid profile) {reference : Naming.Relation (Silmaril.Formats.Git.Arena.Id Name) Payload}
    (computed : ∀ id payload, profile.derive id.lane payload = some id → reference id payload)
    (attested : ∀ id payload, profile.derive id.lane payload = none → profile.attest id payload = true →
      reference id payload) : Naming.Subset arena.observed reference := by
  intro id payload seen
  rcases accepted_provenance (observed_accepted valid seen) with derived | ⟨unavailable, verified⟩
  · exact computed id payload derived
  · exact attested id payload unavailable verified

end Silmaril.Proofs.Formats.Git.Arena
