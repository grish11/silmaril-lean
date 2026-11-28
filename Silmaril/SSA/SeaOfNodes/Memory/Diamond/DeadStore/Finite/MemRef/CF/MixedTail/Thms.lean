module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail

open RVSDG (Locals Port Tuple)
open Quads.CFG (Predecessors)
open Memory.Forwarding.Disjoint (Certificate cell)
open Memory.DeadStore (readAt throughLoad)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open SeaOfNodes.Memory.MLIR.MemRef (observe)
open Silmaril.MLIR.MemRef (Buffer)
open LoadTail.PrefixWord.Sequence.Replay.Search (inferCandidate)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {input : Tuple (Val cells) args}

/-- A covered ordered suffix preserves every Load word and commutes an
incoming write over its entire Load/Store sequence. -/
theorem tail_observations {past : List (List ValueSort)} {live : Nat}
    {body : Memory.Body args past live} {ports : List (Port args .address)}
    (listed : tailPorts body = some ports) (address : Port args .address) (word : Word)
    (valid : (Certificate.mk address ports).Valid input)
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    let written := initial.write (cell input address) word
    let retained := body.denote input locals initial
    body.denote input locals written = (retained.1, retained.2.write (cell input address) word) ∧
      ∀ index, readAt body index input locals written = readAt body index input locals initial :=
  Proofs.tail_observations listed address word valid locals initial

/-- The typed edit removes exactly one Store and preserves every retained
operand. Reapplying the original prefix-produced word restores the full heap. -/
theorem inferCut_observations {past : List (List ValueSort)} {live version : Nat}
    {body : Memory.Body args past live} {edit : LoadTail.PrefixWord.Cut args past live}
    {ports : List (Port args .address)} (found : inferCut version body = some (edit, ports))
    (valid : (Certificate.mk edit.address ports).Valid input) :
    DeletesStores 1 (operations body) (operations edit.retained) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let retained := edit.retained.denote input locals initial
        let word := (edit.beforeStore.denote input locals initial).1
        body.denote input locals initial = (retained.1, retained.2.write (cell input edit.address) word) ∧
          ∀ index, readAt body index input locals initial = readAt edit.retained index input locals initial :=
  Proofs.inferCut_observations found valid

variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {entry : Memory.Graph args} {result : Result cells args preds}

/-- A total refusal means every actual Store version refused. -/
theorem lower_eq_none_iff :
    lower fits arm suffix input entry = none ↔
      ∀ version ∈ storeVersions entry, tryVersion fits arm suffix input entry version = none :=
  List.findSome?_eq_none_iff

/-- A nominated success supplies the exact cut, suffix certificate and
independently admitted original occurrences. -/
theorem tryVersion_checked {version : Nat}
    (accepted : tryVersion fits arm suffix input entry version = some result) :
    result.version = version ∧
      inferCut result.version entry = some (result.emission.edit, result.ports) ∧
      result.facts.Valid input ∧ inferCandidate preds result.emission.edit.address arm = some result.candidate ∧
      (∀ i, LoadTail.PrefixWord.checkArm result.emission.edit.address (arm i) (result.candidate i) input = true) ∧
      result.emission.programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some result.emission.edit.retained) arm suffix⟩ :=
  Proofs.tryVersion_checked accepted

/-- Successful discovery records the actual address certificate, independently
admitted occurrences, saved input and exact emitted pair. -/
theorem lower_checked (accepted : lower fits arm suffix input entry = some result) :
    result.version ∈ storeVersions entry ∧
      inferCut result.version entry = some (result.emission.edit, result.ports) ∧
      result.facts.Valid input ∧ inferCandidate preds result.emission.edit.address arm = some result.candidate ∧
      (∀ i, LoadTail.PrefixWord.checkArm result.emission.edit.address (arm i) (result.candidate i) input = true) ∧
      result.emission.programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some result.emission.edit.retained) arm suffix⟩ :=
  Proofs.lower_checked accepted

/-- The checked nomination preserves the entry Return and each Load word,
and reconstructs the original whole entry buffer. -/
theorem tryVersion_entry {version : Nat}
    (accepted : tryVersion fits arm suffix input entry version = some result) (initial : Buffer cells) :
    let edit := result.emission.edit
    let checkedInput := result.emission.programs.input
    let retained := observe edit.retained checkedInput initial
    let word := (observe edit.beforeStore checkedInput initial).1
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores 1 (operations entry) (operations edit.retained) ∧
      observe entry checkedInput initial = (retained.1, ⟨Heap.write retained.2.cell (cell checkedInput edit.address) word⟩) ∧
      ∀ index, probe entry index = probe edit.retained index :=
  Proofs.tryVersion_entry accepted initial

/-- The emitted entry retains the Return word and each ordered Load word.
The original entry buffer is recovered by reapplying the nominated write. -/
theorem lower_entry (accepted : lower fits arm suffix input entry = some result) (initial : Buffer cells) :
    let edit := result.emission.edit
    let checkedInput := result.emission.programs.input
    let retained := observe edit.retained checkedInput initial
    let word := (observe edit.beforeStore checkedInput initial).1
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores 1 (operations entry) (operations edit.retained) ∧
      observe entry checkedInput initial = (retained.1, ⟨Heap.write retained.2.cell (cell checkedInput edit.address) word⟩) ∧
      ∀ index, probe entry index = probe edit.retained index :=
  Proofs.lower_entry accepted initial

/-- The nominated pair agrees on the selected occurrence, complete join
packet and return observation at every common budget. -/
theorem tryVersion_observations {version : Nat}
    (accepted : tryVersion fits arm suffix input entry version = some result)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.emission.programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial :=
  Proofs.tryVersion_observations accepted arrival fuel initial

/-- At the saved input, the emitted CFGs select the same occurrence and
agree on its join packet, return word and full buffer at every common budget. -/
theorem lower_observations (accepted : lower fits arm suffix input entry = some result)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.emission.programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial :=
  Proofs.lower_observations accepted arrival fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail
