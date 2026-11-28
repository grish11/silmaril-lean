module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail

open RVSDG (Tuple)
open Retained.Load.Static.Sequence.Search
open Discovery.MemRef.CF (entryDestination entryTransition lowerDiamond run)
open Memory.Forwarding.Disjoint (Certificate)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open Final.LoadTail (entryWord)

variable {args : List ValueSort} {cells : Nat}
variable {facts : Certificate args} {input : Tuple (Val cells) args}

/-- Exactly one Store is removed. The retained Store, its typed operand,
and all other operations stay in order. -/
theorem cut_preserves {entry retained : Memory.Graph args} {version : Nat} {store : PrefixStore args}
    (accepted : cut facts version entry = some (store, retained)) (valid : facts.Valid input) (initial : Heap cells) :
    DeletesStores 1 (operations entry) (operations retained) ∧
      entry.denote input initial =
        ((retained.denote input initial).1, (store.table.denote input (retained.denote input initial).2).2) :=
  Proofs.cut_preserves accepted valid initial

variable {graph : Graph args} {entry : Memory.Graph args} {version : Nat} {artifacts : Artifacts cells args}

/-- Emission uses the actual retained table and replays the existing
two-route check. -/
theorem emit_replay (emitted : emit cells graph entry version facts = some artifacts) (input : Tuple (Val cells) args) :
    ∃ store retained edited, cut facts version entry = some (store, retained) ∧
      Discovery.rewrite ⟨store, graph⟩ input = some edited ∧
      artifacts = ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph (some retained)⟩ :=
  Proofs.emit_replay emitted input

/-- The emitted entry preserves its word and exact control packet. Applying
the removed write to the optimized entry buffer recovers the original buffer. -/
theorem emit_entry (emitted : emit cells graph entry version facts = some artifacts)
    (valid : facts.Valid input) (guard : Bool) (initial : Buffer cells) :
    ∃ store retained, cut facts version entry = some (store, retained) ∧
      entryWord artifacts.optimized input initial = entryWord artifacts.original input initial ∧
      let entered := entryTransition artifacts.optimized input guard initial
      entryTransition artifacts.original input guard initial =
        (entered.1, ⟨(store.table.denote input entered.2.cell).2⟩) :=
  Proofs.emit_entry emitted valid guard initial

/-- The emitted successor packet and complete return agree at every
valuation satisfying the certificate. -/
theorem emit_observations (emitted : emit cells graph entry version facts = some artifacts)
    (valid : facts.Valid input) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    entryDestination artifacts.optimized input guard initial = entryDestination artifacts.original input guard initial ∧
      run artifacts.original input guard fuel initial = expected ∧
      run artifacts.optimized input guard fuel initial = expected :=
  Proofs.emit_observations emitted valid guard fuel initial

variable {result : Final.LoadTail.Result cells args}

/-- Replay the first phase and keep its exact artifacts on refusal. -/
theorem lower_checked (emitted : lower graph entry version input facts = .ok result) :
    Inference.lower graph entry input = .ok result.entryOnly ∧
      Retained.Load.Static.Sequence.lower graph entry result.entryOnly.plan input = some result.entryOnly.programs ∧
      match result.routes with
      | none => result.programs = result.entryOnly.programs
      | some artifacts =>
        facts.Valid input ∧ emit cells graph result.entryOnly.entry version facts = some artifacts ∧
          artifacts.original = result.entryOnly.programs.optimized :=
  Proofs.lower_checked emitted

/-- The staged emitted pair preserves the successor packet, returned word,
and full final buffer for either predicate and every CF budget. -/
theorem lower_observations (emitted : lower graph entry version input facts = .ok result)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.programs
    let observed := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (observed.1, Buffer.mk observed.2)
    entryDestination programs.optimized programs.input guard initial =
      entryDestination programs.original programs.input guard initial ∧
      run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_observations emitted guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail
