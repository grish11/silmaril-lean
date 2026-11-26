module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final

open RVSDG (Locals Tuple)
open SeaOfNodes.Diamond (Projection)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Discovery.MemRef.CF (entryDestination entryTransition lowerDiamond run)

variable {args : List ValueSort} {cells : Nat}

/-- Reuse the same cut with a checked disjoint suffix and arbitrary
preceding operations in the native typed table. -/
theorem cutWith_disjoint_preserves {past : List (List ValueSort)} {live version : Nat}
    {body retainedEntry : Memory.Body args past live} {store : PrefixStore args}
    (input : Tuple (Val cells) args)
    (check : PrefixStore args → {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool)
    (safe : ∀ {past : List (List ValueSort)} {live : Nat} (tail : Memory.Body args past live)
      (store : PrefixStore args), check store tail = true → Retained.Load.checkTail store input tail = true)
    (accepted : cutWith check version body = some (store, retainedEntry)) :
    DeletesStores 1 (operations body) (operations retainedEntry) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let retained := retainedEntry.denote input locals initial
        body.denote input locals initial = (retained.1, (store.table.denote input retained.2).2) :=
  Proofs.cutWith_disjoint_preserves input check safe accepted

/-- The cut keeps all earlier operations and scalar wires in order. The
source entry's buffer is the final write on the retained prefix buffer. -/
theorem cut_preserves {past : List (List ValueSort)} {live version : Nat}
    {body retainedEntry : Memory.Body args past live} {store : PrefixStore args}
    (input : Tuple (Val cells) args) (accepted : cut version body = some (store, retainedEntry)) :
    DeletesStores 1 (operations body) (operations retainedEntry) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let retained := retainedEntry.denote input locals initial
        body.denote input locals initial = (retained.1, (store.table.denote input retained.2).2) :=
  Proofs.cut_preserves input accepted

variable {graph : Graph args} {entry retainedEntry : Memory.Graph args} {version : Nat}
variable {store : PrefixStore args} {artifacts : Artifacts cells args}

/-- The emitted edit uses the actual retained prefix and replays through
the existing two-occurrence checker at every input. -/
theorem lower_replay (emitted : lower cells graph entry version = some artifacts) (input : Tuple (Val cells) args) :
    ∃ store retainedEntry edited, cut version entry = some (store, retainedEntry) ∧
      Discovery.rewrite ⟨store, graph⟩ input = some edited ∧
      artifacts = ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph (some retainedEntry)⟩ :=
  Proofs.lower_replay emitted input

/-- The optimized entry passes the entire retained prefix buffer to the
selected original Region occurrence for either predicate. -/
theorem lower_retained_entry (emitted : lower cells graph entry version = some artifacts)
    (accepted : cut version entry = some (store, retainedEntry)) (input : Tuple (Val cells) args)
    (guard : Bool) (initial : Buffer cells) :
    entryTransition artifacts.optimized input guard initial =
      (.inl ⟨.arm (graph.merge.slot (Projection.ofBool guard)), .nil⟩, Buffer.mk (retainedEntry.denote input initial.cell).2) :=
  Proofs.lower_retained_entry emitted accepted input guard initial

/-- Both emitted CFGs select the same successor and agree on the return
and full final buffer for all valuations, initial buffers and budgets. -/
theorem lower_observations (emitted : lower cells graph entry version = some artifacts)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    entryDestination artifacts.optimized input guard initial =
      entryDestination artifacts.original input guard initial ∧
      run artifacts.original input guard fuel initial = expected ∧
      run artifacts.optimized input guard fuel initial = expected :=
  Proofs.lower_observations emitted input guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final
