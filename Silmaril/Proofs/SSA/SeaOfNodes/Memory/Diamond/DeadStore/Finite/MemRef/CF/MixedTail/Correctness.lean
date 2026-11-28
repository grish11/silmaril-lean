module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Proofs

open RVSDG (Locals Port Tuple)
open Quads.CFG (Predecessors)
open Memory.Forwarding.Disjoint (Certificate cell)
open Memory.DeadStore (readAt readAt_load readAt_store reindexMemory_denote reindexMemory_readAt throughLoad)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations reindex_operations)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)
open Silmaril.MLIR.MemRef (Buffer)
open LoadTail.PrefixWord.Sequence.Replay.Search (inferCandidate)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {input : Tuple (Val cells) args}

theorem tail_observations {past : List (List ValueSort)} {live : Nat}
    {body : Memory.Body args past live} {ports : List (Port args .address)}
    (listed : tailPorts body = some ports) (address : Port args .address) (word : Word)
    (valid : (Certificate.mk address ports).Valid input)
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    let written := initial.write (cell input address) word
    let retained := body.denote input locals initial
    body.denote input locals written = (retained.1, retained.2.write (cell input address) word) ∧
      ∀ index, readAt body index input locals written = readAt body index input locals initial := by
  induction body generalizing initial ports with
  | ret => exact ⟨rfl, fun _ => rfl⟩
  | load _ reader _ ih =>
    cases reader with
    | output => contradiction
    | arg reader =>
      obtain ⟨_, rest, packed⟩ := Option.map_eq_some_iff.mp listed
      cases packed
      have distinct := (valid reader (List.mem_cons_self ..)).symm
      have same := initial.read_write_other (cell input address) (cell input reader) word distinct
      obtain ⟨value, reads⟩ := ih rest (fun port member => valid port (List.mem_cons_of_mem _ member))
        (.cons (initial.read (cell input reader)) .nil, locals) initial
      have readArg : readValue (.arg reader) input locals = cell input reader := rfl
      refine ⟨by simpa only [Memory.Body.denote, readArg, same] using value, fun index => ?_⟩
      cases index with
      | zero => exact congrArg some same
      | succ index => simpa only [readAt_load, readArg, same] using reads index
  | store _ writer data _ ih =>
    cases writer with
    | output => contradiction
    | arg writer =>
      obtain ⟨_, rest, packed⟩ := Option.map_eq_some_iff.mp listed
      cases packed
      let value := readValue data input locals
      let updated := initial.write (cell input writer) value
      have commute : (initial.write (cell input address) word).write (cell input writer) (readValue data input locals) =
          updated.write (cell input address) word :=
        Function.update_comm (β := fun _ : Address cells => Word) (valid writer (List.mem_cons_self ..))
          word value initial
      have writeArg : readValue (.arg writer) input locals = cell input writer := rfl
      simpa only [Memory.Body.denote, readAt_store, writeArg, commute] using
        ih rest (fun port member => valid port (List.mem_cons_of_mem _ member)) locals updated

theorem inferCut_observations {past : List (List ValueSort)} {live version : Nat}
    {body : Memory.Body args past live} {edit : LoadTail.PrefixWord.Cut args past live}
    {ports : List (Port args .address)} (found : inferCut version body = some (edit, ports))
    (valid : (Certificate.mk edit.address ports).Valid input) :
    DeletesStores 1 (operations body) (operations edit.retained) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let retained := edit.retained.denote input locals initial
        let word := (edit.beforeStore.denote input locals initial).1
        body.denote input locals initial = (retained.1, retained.2.write (cell input edit.address) word) ∧
          ∀ index, readAt body index input locals initial = readAt edit.retained index input locals initial := by
  induction body with
  | ret => contradiction
  | load _ address _ ih =>
    obtain ⟨⟨_, _⟩, rest, packed⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj packed
    obtain ⟨order, replay⟩ := ih rest valid
    refine ⟨.keep (.load address) order, fun locals initial => ?_⟩
    obtain ⟨value, reads⟩ := replay (.cons (initial.read (readValue address input locals)) .nil, locals) initial
    refine ⟨value, fun index => ?_⟩
    cases index with
    | zero => rfl
    | succ index => simpa only [readAt_load] using reads index
  | @store _ live _ address word rest ih =>
    simp only [inferCut] at found
    split at found
    · split at found
      next selected binding result =>
        obtain ⟨_, listed, packed⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj packed
        constructor
        · simp only [operations, reindex_operations]
          exact .drop _ _ (DeletesStores.refl _)
        · intro locals initial
          simp only [reindexMemory_denote, readAt_store, reindexMemory_readAt]
          exact tail_observations listed selected (readValue (.output binding result) input locals) valid locals initial
      next => contradiction
    · obtain ⟨⟨_, _⟩, rest, packed⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj packed
      obtain ⟨order, replay⟩ := ih rest valid
      refine ⟨.keep (.store address word) order, fun locals initial => ?_⟩
      obtain ⟨value, reads⟩ :=
        replay locals (initial.write (readValue address input locals) (readValue word input locals))
      exact ⟨value, fun index => by simpa only [readAt_store] using reads index⟩

variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {entry : Memory.Graph args} {result : Result cells args preds}

theorem tryVersion_checked {version : Nat}
    (accepted : tryVersion fits arm suffix input entry version = some result) :
    result.version = version ∧
      inferCut result.version entry = some (result.emission.edit, result.ports) ∧
      result.facts.Valid input ∧ inferCandidate preds result.emission.edit.address arm = some result.candidate ∧
      (∀ i, LoadTail.PrefixWord.checkArm result.emission.edit.address (arm i) (result.candidate i) input = true) ∧
      result.emission.programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some result.emission.edit.retained) arm suffix⟩ := by
  obtain ⟨⟨edit, ports⟩, cut, next⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨candidate, inferred, packed⟩ := Option.bind_eq_some_iff.mp next
  dsimp only at packed
  split at packed
  next checked =>
    cases Option.some.inj packed
    obtain ⟨valid, arms⟩ := Bool.and_eq_true_iff.mp checked
    exact ⟨rfl, cut, (Certificate.check_iff_valid _ input).mp valid, inferred,
      fun i => List.all_eq_true.mp arms i (List.mem_finRange i), rfl⟩
  next => contradiction

theorem lower_checked (accepted : lower fits arm suffix input entry = some result) :
    result.version ∈ storeVersions entry ∧
      inferCut result.version entry = some (result.emission.edit, result.ports) ∧
      result.facts.Valid input ∧ inferCandidate preds result.emission.edit.address arm = some result.candidate ∧
      (∀ i, LoadTail.PrefixWord.checkArm result.emission.edit.address (arm i) (result.candidate i) input = true) ∧
      result.emission.programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some result.emission.edit.retained) arm suffix⟩ := by
  obtain ⟨version, member, attempted⟩ := List.exists_of_findSome?_eq_some accepted
  obtain ⟨rfl, checked⟩ := tryVersion_checked attempted
  exact ⟨member, checked⟩

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
      ∀ index, probe entry index = probe edit.retained index := by
  obtain ⟨_, found, valid, _, _, programs⟩ := tryVersion_checked accepted
  obtain ⟨order, replay⟩ := inferCut_observations found valid
  obtain ⟨value, reads⟩ := replay PUnit.unit initial.cell
  simp only [programs, lower_run]
  refine ⟨order, ?_, fun index => ?_⟩
  · exact congrArg (fun result : Word × Heap cells => (result.1, Buffer.mk result.2)) value
  · simpa only [readAt, Memory.Graph.denote] using reads index

theorem lower_entry (accepted : lower fits arm suffix input entry = some result) (initial : Buffer cells) :
    let edit := result.emission.edit
    let checkedInput := result.emission.programs.input
    let retained := observe edit.retained checkedInput initial
    let word := (observe edit.beforeStore checkedInput initial).1
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores 1 (operations entry) (operations edit.retained) ∧
      observe entry checkedInput initial = (retained.1, ⟨Heap.write retained.2.cell (cell checkedInput edit.address) word⟩) ∧
      ∀ index, probe entry index = probe edit.retained index := by
  obtain ⟨_, _, attempted⟩ := List.exists_of_findSome?_eq_some accepted
  exact tryVersion_entry attempted initial

theorem tryVersion_observations {version : Nat}
    (accepted : tryVersion fits arm suffix input entry version = some result)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.emission.programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial := by
  obtain ⟨_, found, valid, _, routes, programs⟩ := tryVersion_checked accepted
  have relation := ((inferCut_observations found valid).2 PUnit.unit initial.cell).1
  have heap := congrArg Prod.snd relation
  have same : (arm arrival).denote input (Memory.Graph.denote result.emission.edit.retained input initial.cell).2 =
      (arm arrival).denote input (entry.denote input initial.cell).2 :=
    (LoadTail.PrefixWord.checkArm_observations (routes arrival) _ _).1.trans (congrArg ((arm arrival).denote input) heap.symm)
  simp only [programs, lowerBank_entry, lowerBank_arm, lower_run, lowerBank_run, same, and_self]

theorem lower_observations (accepted : lower fits arm suffix input entry = some result)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.emission.programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial := by
  obtain ⟨_, _, attempted⟩ := List.exists_of_findSome?_eq_some accepted
  exact tryVersion_observations attempted arrival fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Proofs
