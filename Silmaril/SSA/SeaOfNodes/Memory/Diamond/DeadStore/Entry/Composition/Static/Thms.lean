module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Slot)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryDestination lowerDiamond run)

variable {args : List ValueSort} {cells : Nat}
variable {source : Prefixed args} {candidate : Candidate args} {rewritten : Graph args}
variable {result : Discovery.Result args}

/-- A successful static candidate carries an empty reader list at each
Region occurrence. -/
theorem rewriteWith_readers_empty (accepted : rewriteWith source candidate = some rewritten) (arrival : Slot) :
    (candidate arrival).readers = [] :=
  Proofs.rewriteWith_readers_empty accepted arrival

/-- The structural check produces the exact existing checked result at
every typed input. -/
theorem rewriteWith_replay (accepted : rewriteWith source candidate = some rewritten)
    (input : Tuple (Val cells) args) :
    DeadStore.rewrite source candidate input = some rewritten :=
  Proofs.rewriteWith_replay accepted input

theorem rewrite_replay (accepted : rewrite source = some result) (input : Tuple (Val cells) args) :
    Discovery.rewrite source input = some result :=
  Proofs.rewrite_replay accepted input

theorem rewrite_readers_empty (accepted : rewrite source = some result) (arrival : Slot) :
    (result.candidate arrival).readers = [] :=
  Proofs.rewrite_readers_empty accepted arrival

variable {graph : Graph args} {entry : Memory.Graph args} {artifacts : Artifacts cells args}

/-- Emission reuses the same singleton entry and two checked occurrences
as the existing concrete deletion. -/
theorem lower_replay (emitted : lower cells graph entry = some artifacts) (input : Tuple (Val cells) args) :
    ∃ store result, Composition.asPrefixStore entry = some store ∧
      Discovery.rewrite ⟨store, graph⟩ input = some result ∧
      artifacts = ⟨lowerDiamond cells graph (some entry), lowerDiamond cells result.graph none⟩ :=
  Proofs.lower_replay emitted input

/-- The emitted entry destination packets agree. The selected arm's
overwrite establishes agreement on the word and whole final buffer at
every valuation, predicate, initial buffer, and CF budget. -/
theorem lower_observations (emitted : lower cells graph entry = some artifacts)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    entryDestination artifacts.optimized input guard initial =
      entryDestination artifacts.original input guard initial ∧
      run artifacts.original input guard fuel initial = expected ∧
      run artifacts.optimized input guard fuel initial = expected :=
  Proofs.lower_observations emitted input guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static
