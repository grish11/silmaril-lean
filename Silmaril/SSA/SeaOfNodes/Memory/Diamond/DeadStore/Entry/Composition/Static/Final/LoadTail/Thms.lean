module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail

open RVSDG (Origin Port Tuple)
open Retained.Load.Static.Sequence.Search
open Discovery.MemRef.CF (entryDestination lowerDiamond run)
open Memory.Forwarding.Disjoint (Certificate cell)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations storeCount)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells : Nat}
variable {facts : Certificate args} {input : Tuple (Val cells) args}

/-- A certified read-only suffix passes the existing concrete
disjointness check at every valuation satisfying the certificate. -/
theorem checkTail_disjoint {past : List (List ValueSort)} {live : Nat}
    (tail : Memory.Body args past live) (store : PrefixStore args)
    (safe : checkTail facts store tail = true) (valid : facts.Valid input) :
    Retained.Load.checkTail store input tail = true :=
  Proofs.checkTail_disjoint tail store safe valid

/-- Every admitted reader sees the same word on the retained buffer
and on that buffer with the nominated Store applied. Loads leave that
buffer live for the entire chain. -/
theorem checkTail_read_word {past : List (List ValueSort)} {live : Nat}
    {tail : Memory.Body args past live} {readers : List (Port args .address)}
    (store : PrefixStore args) (valid : facts.Valid input)
    (accepted : checkTail facts store tail = true) (listed : readPorts tail = some readers)
    (reader : Port args .address) (member : reader ∈ readers) (initial : Heap cells) :
    ((store.table.denote input initial).2).read (cell input reader) = initial.read (cell input reader) :=
  Proofs.checkTail_read_word store valid accepted listed reader member initial

/-- The checked Load reads the same word with or without the nominated
write, even when Return exports a different word. -/
theorem checkTail_load_word {past : List (List ValueSort)} {live : Nat}
    {memory returnedMemory : MemoryInput live} {reader : Port args .address}
    {returned : Origin args ([.word] :: past) .word}
    (store : PrefixStore args) (valid : facts.Valid input)
    (accepted : checkTail facts store (.load memory (.arg reader) (.ret returnedMemory returned)) = true)
    (initial : Heap cells) :
    ((store.table.denote input initial).2).read (cell input reader) = initial.read (cell input reader) :=
  Proofs.checkTail_load_word store valid accepted initial

/-- Preserve the retained operations and returned entry word. Applying
the removed write to the retained heap recovers the original heap. -/
theorem cut_preserves {entry retained : Memory.Graph args} {version : Nat} {store : PrefixStore args}
    (accepted : cut facts version entry = some (store, retained)) (valid : facts.Valid input) (initial : Heap cells) :
    DeletesStores 1 (operations entry) (operations retained) ∧
      entry.denote input initial =
        ((retained.denote input initial).1, (store.table.denote input (retained.denote input initial).2).2) :=
  Proofs.cut_preserves accepted valid initial

variable {graph : Graph args} {entry : Memory.Graph args} {version : Nat} {artifacts : Artifacts cells args}

/-- The edit reuses the exact two checked occurrences and retained table. -/
theorem emit_replay (emitted : emit cells graph entry version facts = some artifacts) (input : Tuple (Val cells) args) :
    ∃ store retained edited, cut facts version entry = some (store, retained) ∧
      Discovery.rewrite ⟨store, graph⟩ input = some edited ∧
      artifacts = ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph (some retained)⟩ :=
  Proofs.emit_replay emitted input

/-- The emitted entry body keeps its scalar result, including when it
exports the retained Load. The CF returns agree on the full final buffer. -/
theorem emit_observations (emitted : emit cells graph entry version facts = some artifacts)
    (valid : facts.Valid input) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    entryWord artifacts.optimized input initial = entryWord artifacts.original input initial ∧
      entryDestination artifacts.optimized input guard initial = entryDestination artifacts.original input guard initial ∧
      run artifacts.original input guard fuel initial = expected ∧
      run artifacts.optimized input guard fuel initial = expected :=
  Proofs.emit_observations emitted valid guard fuel initial

variable {result : LoadTail.Result cells args}

/-- Replay the exact entry plan. A refusal keeps its artifact. Success
links the second emitter's original artifact to the first optimized one. -/
theorem lower_checked (emitted : lower graph entry input facts = .ok result) :
    Inference.lower graph entry input = .ok result.entryOnly ∧
      Retained.Load.Static.Sequence.lower graph entry result.entryOnly.plan input = some result.entryOnly.programs ∧
      match result.routes with
      | none => result.programs = result.entryOnly.programs
      | some artifacts =>
        facts.Valid input ∧ emit cells graph result.entryOnly.entry (storeCount result.entryOnly.entry) facts = some artifacts ∧
          artifacts.original = result.entryOnly.programs.optimized :=
  Proofs.lower_checked emitted

/-- The staged emitted CFGs preserve the entry successor packet, word
and whole final buffer for either predicate and every CF budget. -/
theorem lower_observations (emitted : lower graph entry input facts = .ok result)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.programs
    let observed := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (observed.1, Buffer.mk observed.2)
    entryDestination programs.optimized programs.input guard initial =
      entryDestination programs.original programs.input guard initial ∧
      run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_observations emitted guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail
