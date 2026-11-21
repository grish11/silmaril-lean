module

public import Silmaril.Formats.Git.Translate.Graph.Defs
import Silmaril.Proofs.Formats.Git.Graph

public section

namespace Silmaril.Formats.Git.Translate.Graph

variable {Key Source Target Meta : Type} {algorithm : Native.Algorithm}

/-- A plan covers every local edge reachable from the requested typed name. -/
theorem Plan.reaches {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source}
    {root finish : Address Source} (plan : Plan native lookup (.local (kind := root.1)) root.2)
    (reachable : Reaches lookup root finish) : Nonempty (Plan native lookup (.local (kind := finish.1)) finish.2) :=
  Proofs.Formats.Git.Graph.plan_reaches plan reachable

/-- A successful local plan certifies well-founded edges below its root. This
excludes cycles along local edges, not cycles through external repositories. -/
theorem Plan.accessible {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source}
    {kind : Kind} {source : Source} (plan : Plan native lookup (.local (kind := kind)) source) :
    Acc (fun child parent => LocalEdge lookup parent child) (kind, source) :=
  Proofs.Formats.Git.Graph.plan_accessible plan rfl

/-- Reassembling the discovered graph regenerates the exact original preimage
at every local root, with unchanged native child and parent names. -/
theorem Plan.native_exact {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source}
    {kind : Kind} {role : Role kind} {source : Source} (plan : Plan native lookup role source) :
    Native.renderObject native plan.expand = some plan.expected :=
  Proofs.Formats.Git.Graph.plan_native plan

theorem Outcome.rootPair [DecidableEq Key] [DecidableEq Source] [DecidableEq Target]
    {profile : Profile algorithm Key Source Target Meta} {lookup : Lookup Key Source} {kind : Kind} {source : Source}
    (outcome : Outcome profile lookup kind source) :
    outcome.result.trace.pairs kind source outcome.result.target.root :=
  Eq.mp (congrArg (fun name => outcome.result.trace.pairs kind name outcome.result.target.root)
    outcome.exactName) (translate_root_pair profile _ outcome.translated)

/-- Every reachable local address contributes a target name and an exact store
preimage, not just an opaque frontier pair. -/
theorem Outcome.reaches [DecidableEq Key] [DecidableEq Source] [DecidableEq Target]
    {profile : Profile algorithm Key Source Target Meta} {lookup : Lookup Key Source} {kind : Kind} {source : Source}
    (outcome : Outcome profile lookup kind source) {finish : Address Source}
    (reachable : Reaches lookup (kind, source) finish) :
    ∃ (target : Target) (bytes : ByteArray), lookup.observed finish.1 finish.2 bytes ∧
      ⟨finish.1, finish.2, target, some bytes⟩ ∈ outcome.result.trace.events :=
  Proofs.Formats.Git.Graph.outcome_reaches outcome reachable

theorem Outcome.audited [DecidableEq Key] [DecidableEq Source] [DecidableEq Target]
    {profile : Profile algorithm Key Source Target Meta} {lookup : Lookup Key Source} {kind : Kind} {source : Source}
    (outcome : Outcome profile lookup kind source) {wire : Wire Target} (wireOK : wire.Agrees outcome.result.target) :
    Audit outcome.result lookup.observed (nativeNames profile.native) wire (externalNames profile) :=
  Proofs.Formats.Git.Graph.outcome_audited outcome wireOK

/-- The audited root codec uses the original tree and parent slots in order,
including repeated parents, with a target serialization and naming witness. -/
theorem Outcome.commitEvidence [DecidableEq Key] [DecidableEq Source] [DecidableEq Target]
    {profile : Profile algorithm Key Source Target Meta} {lookup : Lookup Key Source} {source : Source}
    (outcome : Outcome profile lookup .commit source) {wire : Wire Target} (wireOK : wire.Agrees outcome.result.target) :
    ∃ (data : Commit Source Source Native.CommitMetadata) (bytes : ByteArray) (tree : Result Source Target)
      (parents : List (Result Source Target)),
      lookup .commit source = .found ⟨.commit data, bytes⟩ ∧ tree.nativeCommit parents data.metadata = data ∧
      CommitEvidence profile tree parents data.metadata outcome.result lookup.observed (nativeNames profile.native) wire :=
  Proofs.Formats.Git.Graph.outcome_commit outcome wireOK

end Silmaril.Formats.Git.Translate.Graph
