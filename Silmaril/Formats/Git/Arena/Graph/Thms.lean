module

public import Silmaril.Formats.Git.Arena.Graph.Defs
import Silmaril.Proofs.Formats.Git.Arena.Graph

public section

namespace Silmaril.Formats.Git.Arena

variable {Name Payload Key Target Meta : Type} {limit : Nat} {algorithm : Native.Algorithm}
variable [DecidableEq Name] [DecidableEq Payload]

theorem State.resolve_found {profile : Profile Name Payload} {arena : State limit Name Payload}
    {reader : Reader Name Payload} {id : Id Name} {kind : Option Kind} {payload : Payload}
    (found : arena.resolve profile reader id kind = .found payload) : arena.Origin profile reader id kind payload :=
  Proofs.Formats.Git.Arena.resolve_found found

namespace GitBackend

variable {backend : GitBackend algorithm limit Name Payload Key} {kind : Kind} {oid : Source algorithm}

theorem inspect_found {binding : Translate.Graph.Binding Key (Source algorithm) kind}
    (found : backend.inspect kind oid = .found binding) :
    ∃ payload, backend.state.Origin backend.profile backend.reader (id algorithm oid) (some kind) payload ∧
      backend.node kind payload = some binding.node ∧ backend.profile.gitBytes algorithm payload = some binding.bytes :=
  Proofs.Formats.Git.Arena.GitBackend.inspect_found found

theorem observed_origin {bytes : ByteArray} (observed : backend.lookup.observed kind oid bytes) :
    ∃ payload, backend.state.Origin backend.profile backend.reader (id algorithm oid) (some kind) payload ∧
      backend.profile.gitBytes algorithm payload = some bytes := Proofs.Formats.Git.Arena.GitBackend.observed_origin observed

/-- Every audited local event comes from actual resident content or a
validated read through a placeholder, never from a name-only assertion. -/
theorem reaches_origin [LinearOrder Key] [DecidableEq Target]
    {profile : Translate.Profile algorithm Key (Source algorithm) Target Meta}
    (outcome : Translate.Graph.Outcome profile backend.lookup kind oid) {finish : Translate.Graph.Address (Source algorithm)}
    (reachable : Translate.Graph.Reaches backend.lookup (kind, oid) finish) :
    ∃ (target : Target) (bytes : ByteArray) (payload : Payload),
      backend.state.Origin backend.profile backend.reader (id algorithm finish.2) (some finish.1) payload ∧
      backend.profile.gitBytes algorithm payload = some bytes ∧
      ⟨finish.1, finish.2, target, some bytes⟩ ∈ outcome.result.trace.events :=
  Proofs.Formats.Git.Arena.GitBackend.reaches_origin outcome reachable

end GitBackend
end Silmaril.Formats.Git.Arena
