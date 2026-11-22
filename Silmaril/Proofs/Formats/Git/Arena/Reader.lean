module

public import Silmaril.Formats.Git.Arena.Reader.Defs
public import Silmaril.Formats.Git.Arena.Thms

public section

namespace Silmaril.Proofs.Formats.Git.Arena.Reader

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena
open Silmaril.Formats.Dasl
open Silmaril.Semantics.Prolly (Block)

variable {Name Payload Value : Type} {limit : Nat}
variable {descriptor : Descriptor Name Value} {read : CasReader Name} {value : Value}
variable {profile : Profile Name Payload} {id : Arena.Id Name} {payload : Payload}
variable {fetch : Reader Name ByteArray} {decode : Arena.Id Name → ByteArray → Option Payload}

theorem descriptor_found : descriptor.read read = .found value ↔
    ∃ bytes, read descriptor.lane descriptor.name = .found bytes ∧ descriptor.decode bytes = some value := by
  cases wire : read descriptor.lane descriptor.name <;> simp [Descriptor.read, Read.andThen, wire]
  rename_i bytes
  cases descriptor.decode bytes <;> simp

theorem descriptor_fault {fault : ReadFault} (failed : (read descriptor.lane descriptor.name).toExcept = .error fault) :
    (descriptor.read read).toExcept = .error fault := by
  cases wire : read descriptor.lane descriptor.name <;> simp_all [Descriptor.read, Read.andThen, Read.toExcept]

theorem prolly_found {Key Item : Type} {name : Name} {block : Block Name Key Item}
    {parse : ByteArray → Option (Shallow Name)} {codec : Encode.PartialCodec (Block Name Key Item) (Shallow Name)}
    {classify : Name → ReadFault → Prolly.Fault Name} :
    read.prolly parse codec classify name = .ok block ↔
      ∃ bytes shallow, read .object name = .found bytes ∧ parse bytes = some shallow ∧
        codec.decode? shallow = some block := by
  cases wire : read .object name <;> simp [CasReader.prolly, Read.toExcept, wire, Bind.bind, Except.bind, Except.mapError]
  rename_i bytes
  cases parse bytes <;> simp [Prolly.readBlock]
  rename_i shallow
  cases codec.decode? shallow <;> simp

theorem exact_found : Reader.exact profile decode fetch id = .found payload ↔
    ∃ bytes, fetch id = .found bytes ∧ decode id bytes = some payload ∧ profile.wire id payload = some bytes := by
  cases got : fetch id <;> simp [Reader.exact, got]
  rename_i bytes
  cases decoded : decode id bytes <;> simp
  rename_i actual
  by_cases exactBytes : profile.wire id actual = some bytes <;> simp_all
  all_goals intro same; subst payload; assumption

variable [DecidableEq Name] [DecidableEq Payload]
variable {arena after : State limit Name Payload} {key : Fin limit}

theorem cache_at (cached : arena.cacheBytes profile key id decode fetch = .ok (payload, after)) :
    ∃ cell, after key = some cell ∧ cell.payload = some payload := by
  obtain ⟨cell, here, _, hit | fill⟩ := State.cache_spec cached
  · exact ⟨cell, hit.2.symm ▸ here, hit.1⟩
  · exact ⟨{cell with payload := some payload}, State.materialize_spec here fill.2.2, rfl⟩

theorem cache_then_assign {lane : Lane} {result : Loaded limit Name Payload}
    (loaded : arena.cacheAndAssign profile key id lane decode fetch = .ok result) :
    ∃ cached, arena.cacheBytes profile key id decode fetch = .ok (result.payload, cached) ∧
      (match result.derivation with
        | .error fault => cached.assign profile key lane = .error fault ∧ result.arena = cached
        | .ok derived => cached.assign profile key lane = .ok (derived, result.arena)) := by
  cases fetched : arena.cacheBytes profile key id decode fetch with
  | error fault => simp [State.cacheAndAssign, fetched, Bind.bind, Except.bind] at loaded
  | ok value =>
    obtain ⟨value, cached⟩ := value
    cases assigned : cached.assign profile key lane with
    | error fault =>
      simp [State.cacheAndAssign, fetched, assigned, Bind.bind, Except.bind, Pure.pure, Except.pure] at loaded
      subst result
      exact ⟨cached, rfl, assigned, rfl⟩
    | ok named =>
      obtain ⟨derived, after⟩ := named
      simp [State.cacheAndAssign, fetched, assigned, Bind.bind, Except.bind, Pure.pure, Except.pure] at loaded
      subst result
      exact ⟨cached, rfl, assigned⟩

private theorem assign_observed {derived : Arena.Id Name} {lane : Lane}
    (atKey : ∃ cell, arena key = some cell ∧ cell.payload = some payload)
    (assigned : arena.assign profile key lane = .ok (derived, after)) :
    profile.derive lane payload = some derived ∧ after.observed derived payload := by
  obtain ⟨cell, here, resident⟩ := atKey
  obtain ⟨old, actual, found, stored, derivedName, stepped⟩ := State.assign_spec assigned
  have sameCell : old = cell := Option.some.inj (found.symm.trans here)
  subst old
  have samePayload := Option.some.inj (stored.symm.trans resident)
  subst actual
  obtain ⟨next, edited, nextAt, _, _, _⟩ := State.step_spec.mp stepped
  have eq : next = { cell with name := some ((Cell.claims cell).attach derived none) } := by
    simpa [Edit.apply, Arena.Compatible, here, eq_comm] using edited
  have named : derived ∈ (Cell.claims next).ids := by
    rw [eq]
    change derived ∈ ((Cell.claims cell).attach derived none).ids
    by_cases prev : derived ∈ (Cell.claims cell).ids <;> simp [Claims.attach, prev]
  exact ⟨derivedName, key, next, nextAt, named, eq ▸ resident⟩

theorem cache_assigned_valid {lane : Lane} {result : Loaded limit Name Payload}
    (valid : arena.Valid profile)
    (loaded : arena.cacheAndAssign profile key id lane decode fetch = .ok result) :
    result.arena.Valid profile ∧ result.arena.observed id result.payload ∧
      (∀ derived, result.derivation = .ok derived → profile.derive lane result.payload = some derived ∧
        result.arena.observed derived result.payload) := by
  obtain ⟨cached, got, named⟩ := cache_then_assign loaded
  obtain ⟨validCache, _, observed⟩ := State.cache_valid_observed valid got
  cases outcome : result.derivation with
  | error fault =>
    rw [outcome] at named
    obtain ⟨_, post⟩ := named
    rw [post]
    exact ⟨validCache, observed, by simp⟩
  | ok derived =>
    have assigned : cached.assign profile key lane = .ok (derived, result.arena) := by simpa [outcome] using named
    obtain ⟨_, _, _, _, _, attached⟩ := State.assign_spec assigned
    refine ⟨State.valid_step validCache attached, State.extends_observed (State.step_extends attached) observed, ?_⟩
    intro other eq
    cases eq
    exact assign_observed (cache_at got) assigned

theorem cache_assigned_extends {lane : Lane} {result : Loaded limit Name Payload}
    (loaded : arena.cacheAndAssign profile key id lane decode fetch = .ok result) : arena.Extends result.arena := by
  obtain ⟨cached, got, named⟩ := cache_then_assign loaded
  have captured : arena.Extends cached := by
    obtain ⟨_, _, _, hit | fill⟩ := State.cache_spec got
    · rw [hit.2]
      exact fun _ old here => ⟨old, here, fun _ member => member, fun _ member => member, fun _ member => member⟩
    · exact State.step_extends fill.2.2
  cases outcome : result.derivation with
  | error fault =>
    rw [outcome] at named
    exact named.2.symm ▸ captured
  | ok derived =>
    have assigned : cached.assign profile key lane = .ok (derived, result.arena) := by simpa [outcome] using named
    obtain ⟨_, _, _, _, _, attached⟩ := State.assign_spec assigned
    intro query prior present
    obtain ⟨middle, here, before⟩ := captured query prior present
    obtain ⟨latest, now, kept⟩ := State.step_extends attached query middle here
    exact ⟨latest, now, fun _ member => kept.1 (before.1 member),
      fun item => kept.2.1 item ∘ before.2.1 item, fun kind => kept.2.2 kind ∘ before.2.2 kind⟩

end Silmaril.Proofs.Formats.Git.Arena.Reader
