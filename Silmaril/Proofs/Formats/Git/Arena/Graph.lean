module

public import Silmaril.Formats.Git.Arena.Graph.Defs

public section

namespace Silmaril.Proofs.Formats.Git.Arena

open Silmaril.Formats.Git Silmaril.Formats.Git.Arena

variable {Name Payload Key Target Meta : Type} {limit : Nat} {algorithm : Native.Algorithm}
variable [DecidableEq Name] [DecidableEq Payload]

theorem resolve_found {profile : Profile Name Payload} {arena : State limit Name Payload} {reader : Reader Name Payload}
    {id : Silmaril.Formats.Git.Arena.Id Name} {kind : Option Kind} {payload : Payload}
    (found : arena.resolve profile reader id kind = .found payload) : arena.Origin profile reader id kind payload := by
  cases looked : arena.lookup profile id kind <;> simp [State.resolve, looked] at found
  · cases fetched : reader id <;> simp [fetched] at found
    rename_i value
    split at found
    · rename_i allowed
      cases found
      exact .inr ⟨looked, fetched, allowed⟩
    · contradiction
  · cases found
    exact .inl (State.lookup_found_observed looked)

namespace GitBackend

open Silmaril.Formats.Git.Arena.GitBackend

variable {backend : GitBackend algorithm limit Name Payload Key} {kind : Kind} {oid : Source algorithm}
variable {binding : Translate.Graph.Binding Key (Source algorithm) kind}

theorem inspect_found (found : backend.inspect kind oid = .found binding) :
    ∃ payload, backend.state.Origin backend.profile backend.reader (id algorithm oid) (some kind) payload ∧
      backend.node kind payload = some binding.node ∧ backend.profile.gitBytes algorithm payload = some binding.bytes := by
  cases resolved : backend.state.resolve backend.profile backend.reader (id algorithm oid) (some kind) <;>
    simp [inspect, resolved, Read.andThen] at found
  rename_i value
  cases node : backend.node kind value <;> simp [node, Read.ofOption] at found
  cases bytes : backend.profile.gitBytes algorithm value <;> simp [bytes] at found
  subst binding
  exact ⟨value, resolve_found resolved, node, bytes⟩

theorem lookup_found (found : backend.lookup kind oid = .found binding) : backend.inspect kind oid = .found binding := by
  cases inspected : backend.inspect kind oid <;> simp [lookup, inspected] at found
  exact congrArg Read.found found

theorem observed_origin {bytes : ByteArray} (observed : backend.lookup.observed kind oid bytes) :
    ∃ payload, backend.state.Origin backend.profile backend.reader (id algorithm oid) (some kind) payload ∧
      backend.profile.gitBytes algorithm payload = some bytes := by
  cases bound : backend.lookup kind oid <;> simp [Translate.Graph.Lookup.observed, bound] at observed
  obtain ⟨payload, origin, _, encoded⟩ := inspect_found (lookup_found bound)
  exact ⟨payload, origin, observed ▸ encoded⟩

theorem reaches_origin [LinearOrder Key] [DecidableEq Target]
    {profile : Translate.Profile algorithm Key (Source algorithm) Target Meta}
    (outcome : Translate.Graph.Outcome profile backend.lookup kind oid) {finish : Translate.Graph.Address (Source algorithm)}
    (reachable : Translate.Graph.Reaches backend.lookup (kind, oid) finish) :
    ∃ (target : Target) (bytes : ByteArray) (payload : Payload),
      backend.state.Origin backend.profile backend.reader (id algorithm finish.2) (some finish.1) payload ∧
      backend.profile.gitBytes algorithm payload = some bytes ∧
      ⟨finish.1, finish.2, target, some bytes⟩ ∈ outcome.result.trace.events := by
  obtain ⟨target, bytes, observed, event⟩ := outcome.reaches reachable
  obtain ⟨payload, origin, encoded⟩ := observed_origin observed
  exact ⟨target, bytes, payload, origin, encoded, event⟩

end GitBackend
end Silmaril.Proofs.Formats.Git.Arena
