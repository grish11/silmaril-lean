module

public import Silmaril.Formats.Git.Arena.Reader.Defs
public import Silmaril.Formats.Git.Arena.Thms
import Silmaril.Proofs.Formats.Git.Arena.Reader

public section

namespace Silmaril.Formats.Git.Arena

open Silmaril.Semantics.Prolly (Block)

variable {Name Payload Value : Type} {limit : Nat}
variable {descriptor : Descriptor Name Value} {read : CasReader Name} {value : Value}

theorem Descriptor.read_found : descriptor.read read = .found value ↔
    ∃ bytes, read descriptor.lane descriptor.name = .found bytes ∧ descriptor.decode bytes = some value :=
  Proofs.Formats.Git.Arena.Reader.descriptor_found

theorem Descriptor.read_fault {fault : ReadFault}
    (failed : (read descriptor.lane descriptor.name).toExcept = .error fault) :
    (descriptor.read read).toExcept = .error fault :=
  Proofs.Formats.Git.Arena.Reader.descriptor_fault failed

theorem CasReader.prolly_found {Key Item : Type} {name : Name} {block : Block Name Key Item}
    {parse : ByteArray → Option (Dasl.Shallow Name)}
    {codec : Dasl.Encode.PartialCodec (Block Name Key Item) (Dasl.Shallow Name)}
    {classify : Name → ReadFault → Dasl.Prolly.Fault Name} :
    read.prolly parse codec classify name = .ok block ↔
      ∃ bytes shallow, read .object name = .found bytes ∧ parse bytes = some shallow ∧
        codec.decode? shallow = some block :=
  Proofs.Formats.Git.Arena.Reader.prolly_found

variable {profile : Profile Name Payload} {id : Id Name} {payload : Payload}
variable {fetch : Reader Name ByteArray} {decode : Id Name → ByteArray → Option Payload}

theorem Reader.exact_found : Reader.exact profile decode fetch id = .found payload ↔
    ∃ bytes, fetch id = .found bytes ∧ decode id bytes = some payload ∧ profile.wire id payload = some bytes :=
  Proofs.Formats.Git.Arena.Reader.exact_found

variable [DecidableEq Name] [DecidableEq Payload]
variable {arena after : State limit Name Payload} {key : Fin limit} {lane : Lane}

/-- A successful descriptor read from the arena uses a resident binding,
actual serialized bytes in the requested lane, and the descriptor decoder. -/
theorem State.descriptor_found (found : descriptor.read (arena.casReader profile) = .found value) :
    ∃ (payload : Payload) (bytes : ByteArray), arena.observed (.cas descriptor.lane descriptor.name) payload ∧
      profile.wire (.cas descriptor.lane descriptor.name) payload = some bytes ∧
      descriptor.decode bytes = some value := by
  obtain ⟨bytes, read, decoded⟩ := Descriptor.read_found.mp found
  obtain ⟨payload, seen, wire⟩ := State.readWire_found read
  exact ⟨payload, bytes, seen, wire, decoded⟩

theorem State.cacheBytes_spec (cached : arena.cacheBytes profile key id decode fetch = .ok (payload, after)) :
    ∃ cell : Cell Name Payload, arena key = some cell ∧ id ∈ cell.claims.ids ∧
      ((cell.payload = some payload ∧ after = arena) ∨
        (cell.payload = none ∧ (∃ bytes, fetch id = .found bytes ∧ decode id bytes = some payload ∧
          profile.wire id payload = some bytes) ∧ arena.step profile key (.materialize payload) = .ok after)) := by
  obtain ⟨cell, here, named, outcome⟩ := State.cache_spec cached
  exact ⟨cell, here, named, outcome.imp_right fun ⟨empty, hit, filled⟩ => ⟨empty, Reader.exact_found.mp hit, filled⟩⟩

theorem State.cacheBytes_at (cached : arena.cacheBytes profile key id decode fetch = .ok (payload, after)) :
    ∃ cell, after key = some cell ∧ cell.payload = some payload :=
  Proofs.Formats.Git.Arena.Reader.cache_at cached

theorem State.cacheAndAssign_spec {result : Loaded limit Name Payload}
    (loaded : arena.cacheAndAssign profile key id lane decode fetch = .ok result) :
    ∃ cached, arena.cacheBytes profile key id decode fetch = .ok (result.payload, cached) ∧
      (match result.derivation with
        | .error fault => cached.assign profile key lane = .error fault ∧ result.arena = cached
        | .ok derived => cached.assign profile key lane = .ok (derived, result.arena)) :=
  Proofs.Formats.Git.Arena.Reader.cache_then_assign loaded

theorem State.cacheAndAssign_valid {result : Loaded limit Name Payload} (valid : arena.Valid profile)
    (loaded : arena.cacheAndAssign profile key id lane decode fetch = .ok result) :
    result.arena.Valid profile ∧ result.arena.observed id result.payload ∧
      (∀ derived, result.derivation = .ok derived → profile.derive lane result.payload = some derived ∧
        result.arena.observed derived result.payload) :=
  Proofs.Formats.Git.Arena.Reader.cache_assigned_valid valid loaded

/-- Preserve prior claims, payloads and kind hints, even when secondary naming fails. -/
theorem State.cacheAndAssign_extends {result : Loaded limit Name Payload}
    (loaded : arena.cacheAndAssign profile key id lane decode fetch = .ok result) : arena.Extends result.arena :=
  Proofs.Formats.Git.Arena.Reader.cache_assigned_extends loaded

end Silmaril.Formats.Git.Arena
