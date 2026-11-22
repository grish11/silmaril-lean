module

public import Silmaril.Formats.Git.Arena.Defs
import Silmaril.Proofs.Formats.Git.Arena.Basic

public section

namespace Silmaril.Formats.Git.Arena

open Silmaril.Semantics

variable {Name Payload : Type} {limit : Nat}
variable {profile : Profile Name Payload} {arena after : State limit Name Payload} {key : Fin limit}
variable {id : Id Name} {payload : Payload}

/-- Different derived names in one fixed lane and profile imply different
payloads. The converse needs a binding assumption, not a digest label. -/
theorem Profile.different_derived {other : Id Name} {second : Payload} {lane : Lane}
    (first : profile.derive lane payload = some id) (last : profile.derive lane second = some other)
    (different : id ≠ other) : payload ≠ second := by
  rintro rfl
  exact different (Option.some.inj (first.symm.trans last))

theorem State.codecView_keyName {Target : Type} (codec : Dasl.Arena.Codec (Claims Name) Payload Target) :
    Semantics.Arena.State.keyName (arena.codecView codec) key = Semantics.Arena.State.keyName arena key := by
  cases hit : arena key <;> simp [State.codecView, Dasl.Arena.Converter.discard,
    Dasl.Arena.Converter.discardCell, Semantics.Arena.State.keyName, hit]

theorem State.extends_observed (extended : arena.Extends after) : Naming.Subset arena.observed after.observed :=
  Proofs.Formats.Git.Arena.extends_observed extended

variable [DecidableEq Name]

theorem State.empty_valid (profile : Profile Name Payload) :
    State.Valid (limit := limit) profile Semantics.Arena.State.empty := Proofs.Formats.Git.Arena.empty_valid profile

theorem State.observed_binding (coherent : arena.Coherent profile) : Naming.Binding arena.observed :=
  Proofs.Formats.Git.Arena.coherent_binding coherent

theorem State.observed_provenance (valid : arena.Valid profile) (seen : arena.observed id payload) :
    profile.derive id.lane payload = some id ∨
      (profile.derive id.lane payload = none ∧ profile.attest id payload = true) :=
  Proofs.Formats.Git.Arena.accepted_provenance (Proofs.Formats.Git.Arena.observed_accepted valid seen)

/-- A reference relation needs independent evidence for both computed and
attested names; checking a claimed OID alone supplies neither hypothesis. -/
theorem State.observed_refines (valid : arena.Valid profile) {reference : Naming.Relation (Id Name) Payload}
    (computed : ∀ id payload, profile.derive id.lane payload = some id → reference id payload)
    (attested : ∀ id payload, profile.derive id.lane payload = none → profile.attest id payload = true →
      reference id payload) : Naming.Subset arena.observed reference :=
  Proofs.Formats.Git.Arena.observed_refines valid computed attested

theorem State.mem_candidates {cell : Cell Name Payload} :
    cell ∈ arena.candidates id ↔ ∃ key : Fin limit, arena key = some cell ∧ id ∈ cell.claims.ids :=
  Proofs.Formats.Git.Arena.mem_candidates

variable [DecidableEq Payload]

theorem State.step_spec {edit : Edit Name Payload} :
    arena.step profile key edit = .ok after ↔
    ∃ cell : Cell Name Payload, edit.apply (arena key) = .ok cell ∧ after key = some cell ∧ cell.Valid profile ∧
      after.Coherent profile ∧ ∀ query, key ≠ query → after query = arena query :=
  Proofs.Formats.Git.Arena.step_spec

theorem State.valid_step {edit : Edit Name Payload} (valid : arena.Valid profile)
    (stepped : arena.step profile key edit = .ok after) : after.Valid profile :=
  Proofs.Formats.Git.Arena.valid_step valid stepped

/-- No successful insertion, attachment or materialization forgets an old
claim, known kind or payload. In particular, observed bindings cannot rebind. -/
theorem State.step_extends {edit : Edit Name Payload} (stepped : arena.step profile key edit = .ok after) :
    arena.Extends after := Proofs.Formats.Git.Arena.step_extends stepped

theorem State.reserve_spec (kind : Option Kind) (reserved : arena.step profile key (.reserve id kind) = .ok after) :
    arena key = none ∧ after key = some ⟨some ⟨[id], kind⟩, none⟩ :=
  Proofs.Formats.Git.Arena.reserve_spec kind reserved

theorem State.insert_spec (inserted : arena.step profile key (.insert payload) = .ok after) :
    arena key = none ∧ after key = some ⟨none, some payload⟩ := Proofs.Formats.Git.Arena.insert_spec inserted

theorem State.materialize_spec {old : Cell Name Payload} (here : arena key = some old)
    (filled : arena.step profile key (.materialize payload) = .ok after) :
    after key = some { old with payload := some payload } := Proofs.Formats.Git.Arena.materialize_spec here filled

theorem State.assign_spec {lane : Lane} (assigned : arena.assign profile key lane = .ok (id, after)) :
    ∃ (cell : Cell Name Payload) (payload : Payload), arena key = some cell ∧ cell.payload = some payload ∧
      profile.derive lane payload = some id ∧ arena.step profile key (.attach id none) = .ok after :=
  Proofs.Formats.Git.Arena.assign_spec assigned

/-- Claim-first and content-first interleavings give the same arena when
both paths succeed, not when either path violates validation or agreement. -/
theorem State.insert_attach_commutes {reserved inserted attached : State limit Name Payload} (kind : Option Kind)
    (reserve : arena.step profile key (.reserve id kind) = .ok reserved)
    (fill : reserved.step profile key (.materialize payload) = .ok after)
    (insert : arena.step profile key (.insert payload) = .ok inserted)
    (attach : inserted.step profile key (.attach id kind) = .ok attached) : after = attached :=
  Proofs.Formats.Git.Arena.insert_attach_commutes kind reserve fill insert attach

theorem State.cache_spec {read : Reader Name Payload} (cached : arena.cache profile key id read = .ok (payload, after)) :
    ∃ cell : Cell Name Payload, arena key = some cell ∧ id ∈ cell.claims.ids ∧
      ((cell.payload = some payload ∧ after = arena) ∨
       (cell.payload = none ∧ read id = .found payload ∧
         arena.step profile key (.materialize payload) = .ok after)) := Proofs.Formats.Git.Arena.cache_spec cached

theorem State.cache_valid_observed {read : Reader Name Payload} (valid : arena.Valid profile)
    (cached : arena.cache profile key id read = .ok (payload, after)) :
    after.Valid profile ∧ arena.Extends after ∧ after.observed id payload :=
  Proofs.Formats.Git.Arena.cache_valid_observed valid cached

theorem State.lookup_found_observed {expect : Option Kind} (found : arena.lookup profile id expect = .found payload) :
    arena.observed id payload := Proofs.Formats.Git.Arena.lookup_found_observed found

theorem State.lookup_found_iff (coherent : arena.Coherent profile) :
    arena.lookup profile id = .found payload ↔ arena.observed id payload :=
  ⟨Proofs.Formats.Git.Arena.lookup_found_observed, Proofs.Formats.Git.Arena.lookup_found_of_observed coherent⟩

theorem State.readWire_found {expect : Option Kind} {bytes : ByteArray}
    (found : arena.readWire profile id expect = .found bytes) :
    ∃ payload, arena.observed id payload ∧ profile.wire id payload = some bytes :=
  Proofs.Formats.Git.Arena.readWire_found found

end Silmaril.Formats.Git.Arena
