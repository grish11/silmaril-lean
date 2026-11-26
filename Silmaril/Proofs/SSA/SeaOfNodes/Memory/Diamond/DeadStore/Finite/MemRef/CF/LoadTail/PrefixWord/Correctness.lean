module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms
import Mathlib.Data.Fin.Basic

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Proofs

open RVSDG (Locals Tuple)
open Memory.Forwarding.Disjoint (Certificate cell)
open Memory.DeadStore (readAt readAt_load readAt_store reindexMemory_readAt throughLoad)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations reindex_operations)
open DeadStore.Entry.Composition.Static.Final.LoadTail (checkTailAddress_transfer checkTailAddress_readbacks)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)

variable {args : List ValueSort} {cells sites : Nat} {preds : Quads.CFG.Predecessors sites}
variable {facts : Certificate args} {input : Tuple (Val cells) args} {version : Nat}

private theorem cut_observations {past : List (List ValueSort)} {live : Nat}
    {body : Memory.Body args past live} {edit : Cut args past live}
    (accepted : cut facts version body = some edit) (valid : facts.Valid input) :
    DeletesStores 1 (operations body) (operations edit.retained) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let pre := edit.beforeStore.denote input locals initial
        let retained := edit.retained.denote input locals initial
        retained.2 = pre.2 ∧
          body.denote input locals initial = (retained.1, pre.2.write (cell input edit.address) pre.1) ∧
          ∀ index, readAt body index input locals initial = readAt edit.retained index input locals initial := by
  induction body with
  | ret => contradiction
  | load _ address _ ih =>
    obtain ⟨_, checked, rfl⟩ := Option.map_eq_some_iff.mp accepted
    obtain ⟨order, same⟩ := ih checked
    refine ⟨.keep (.load address) order, ?_⟩
    intro locals initial
    obtain ⟨heap, result, reads⟩ :=
      same (.cons (initial.read (readValue address input locals)) .nil, locals) initial
    refine ⟨heap, result, fun index => ?_⟩
    cases index with
    | zero => rfl
    | succ index => simpa only [readAt_load] using reads index
  | @store _ live _ address word rest ih =>
    simp only [cut] at accepted
    split at accepted
    · split at accepted
      next selected binding result =>
        split at accepted
        next safe =>
          cases Option.some.inj accepted
          constructor
          · simp only [operations, reindex_operations]
            exact .drop _ _ (DeletesStores.refl _)
          · intro locals initial
            dsimp only
            simp only [Memory.DeadStore.reindexMemory_denote, readAt_store, reindexMemory_readAt]
            let word := readValue (.output binding result) input locals
            have transfer := checkTailAddress_transfer rest selected word valid safe locals initial
            refine ⟨?_, transfer.2, checkTailAddress_readbacks rest selected word valid safe locals initial⟩
            change (rest.denote input locals initial).2 = initial
            exact congrArg Prod.snd transfer.1
        next => contradiction
      next => contradiction
    · obtain ⟨_, checked, rfl⟩ := Option.map_eq_some_iff.mp accepted
      obtain ⟨order, same⟩ := ih checked
      refine ⟨.keep (.store address word) order, ?_⟩
      intro locals initial
      obtain ⟨heap, result, reads⟩ :=
        same locals (initial.write (readValue address input locals) (readValue word input locals))
      exact ⟨heap, result, fun index => by simpa only [readAt_store] using reads index⟩

theorem cut_preserves {past : List (List ValueSort)} {live : Nat}
    {body : Memory.Body args past live} {edit : Cut args past live}
    (accepted : cut facts version body = some edit) (valid : facts.Valid input) :
    DeletesStores 1 (operations body) (operations edit.retained) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let pre := edit.beforeStore.denote input locals initial
        let retained := edit.retained.denote input locals initial
        retained.2 = pre.2 ∧
          body.denote input locals initial = (retained.1, pre.2.write (cell input edit.address) pre.1) := by
  obtain ⟨order, observed⟩ := cut_observations accepted valid
  exact ⟨order, fun locals initial => ⟨(observed locals initial).1, (observed locals initial).2.1⟩⟩

theorem cut_readbacks {past : List (List ValueSort)} {live : Nat}
    {body : Memory.Body args past live} {edit : Cut args past live}
    (accepted : cut facts version body = some edit) (valid : facts.Valid input)
    (locals : Locals (Val cells) past) (initial : Heap cells) (index : Nat) :
    readAt body index input locals initial = readAt edit.retained index input locals initial :=
  (cut_observations accepted valid).2 locals initial |>.2.2 index

theorem checkArm_observations {address : RVSDG.Port args .address} {arm : Memory.Graph args}
    {witness : ArmOverwrite args} (checked : checkArm address arm witness input = true)
    (initial : Heap cells) (word : Word) :
    let written := initial.write (cell input address) word
    arm.denote input initial = arm.denote input written ∧
      ∀ index, Memory.DeadStore.readAt arm index input PUnit.unit initial =
        Memory.DeadStore.readAt arm index input PUnit.unit written := by
  obtain ⟨valid, safe⟩ := Bool.and_eq_true_iff.mp checked
  exact Memory.DeadStore.noReadUntil_write witness.storeVersion arm input
    ((Certificate.check_iff_valid ⟨address, witness.readers⟩ input).mp valid) initial word safe

variable {fits : Fits preds} {entry : Memory.Graph args}
variable {arm : Occurrence preds → Memory.Graph args} {candidate : Candidate args preds}
variable {suffix : Memory.Graph (.word :: args)} {programs : Programs cells args preds}

theorem lower_eq_map_lowerWithEntry :
    lower preds fits entry version arm candidate suffix input facts =
      (lowerWithEntry preds fits entry version arm candidate suffix input facts).map Emission.programs := by
  cases checked : cut facts version entry <;> simp [lower, lowerWithEntry, checked]

theorem lowerWithEntry_replay {emission : Emission cells args preds}
    (emitted : lowerWithEntry preds fits entry version arm candidate suffix input facts = some emission) :
    cut facts version entry = some emission.edit ∧ facts.Valid input ∧
      (∀ i, checkArm emission.edit.address (arm i) (candidate i) input = true) ∧
      emission.programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some emission.edit.retained) arm suffix⟩ := by
  obtain ⟨edit, accepted, packed⟩ := Option.bind_eq_some_iff.mp emitted
  split at packed
  next checked =>
    cases Option.some.inj packed
    obtain ⟨valid, arms⟩ := Bool.and_eq_true_iff.mp checked
    exact ⟨accepted, (facts.check_iff_valid input).mp valid,
      fun i => List.all_eq_true.mp arms i (List.mem_finRange i), rfl⟩
  next => contradiction

theorem lower_replay (emitted : lower preds fits entry version arm candidate suffix input facts = some programs) :
    ∃ edit, cut facts version entry = some edit ∧ facts.Valid input ∧
      (∀ i, checkArm edit.address (arm i) (candidate i) input = true) ∧
      programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some edit.retained) arm suffix⟩ := by
  rw [lower_eq_map_lowerWithEntry] at emitted
  obtain ⟨emission, accepted, rfl⟩ := Option.map_eq_some_iff.mp emitted
  exact ⟨emission.edit, lowerWithEntry_replay accepted⟩

theorem lower_readbacks (emitted : lower preds fits entry version arm candidate suffix input facts = some programs)
    {edit : Cut args [] 0} (accepted : cut facts version entry = some edit)
    (index : Nat) (initial : Buffer cells) :
    let probe := fun (graph : Memory.Graph args) => (throughLoad graph index).map fun block =>
      (observe block programs.input initial).1
    probe entry = probe edit.retained := by
  obtain ⟨_, cutEq, valid, _, rfl⟩ := lower_replay emitted
  rw [accepted] at cutEq
  cases Option.some.inj cutEq
  simpa only [readAt, lower_run, Memory.Graph.denote] using
    cut_readbacks accepted valid PUnit.unit initial.cell index

theorem lower_entry (emitted : lower preds fits entry version arm candidate suffix input facts = some programs)
    {edit : Cut args [] 0} (accepted : cut facts version entry = some edit)
    (arrival : Occurrence preds) (initial : Buffer cells) :
    DeletesStores 1 (operations entry) (operations edit.retained) ∧
    let pre := observe edit.beforeStore programs.input initial
    let retained := observe edit.retained programs.input initial
    let restored := Buffer.mk (Heap.write pre.2.cell (cell programs.input edit.address) pre.1)
    retained.2 = pre.2 ∧ observe entry programs.input initial = (retained.1, restored) ∧
      entryTransition programs.original programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, restored) ∧
      entryTransition programs.optimized programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, retained.2) := by
  obtain ⟨_, cutEq, valid, _, rfl⟩ := lower_replay emitted
  rw [accepted] at cutEq
  cases Option.some.inj cutEq
  obtain ⟨order, replay⟩ := cut_preserves accepted valid
  obtain ⟨heap, same⟩ := replay PUnit.unit initial.cell
  refine ⟨order, ?_, ?_, ?_, ?_⟩
  · simp only [lower_run]
    exact congrArg Buffer.mk heap
  · simp only [lower_run]
    exact congrArg (fun result : Word × Heap cells => (result.1, Buffer.mk result.2)) same
  · simp only [lowerBank_entry, lower_run]
    exact Prod.ext rfl (congrArg Buffer.mk (congrArg Prod.snd same))
  · simp only [lowerBank_entry, lower_run]

theorem lower_observations (emitted : lower preds fits entry version arm candidate suffix input facts = some programs)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    let packet := (arm arrival).denote input (entry.denote input initial.cell).2
    let result := suffix.denote (.cons packet.1 input) packet.2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.original programs.input arrival fuel initial = expected ∧
      run programs.optimized programs.input arrival fuel initial = expected := by
  obtain ⟨edit, accepted, valid, checked, rfl⟩ := lower_replay emitted
  obtain ⟨heap, replay⟩ := (cut_preserves accepted valid).2 PUnit.unit initial.cell
  have same : (arm arrival).denote input (Memory.Graph.denote edit.retained input initial.cell).2 =
      (arm arrival).denote input (entry.denote input initial.cell).2 := by
    change (arm arrival).denote input (edit.retained.denote input PUnit.unit initial.cell).2 =
      (arm arrival).denote input (Memory.Body.denote input entry PUnit.unit initial.cell).2
    rw [congrArg Prod.snd replay, heap]
    exact (checkArm_observations (checked arrival) _ _).1
  simp only [lowerBank_entry, lowerBank_arm, lower_run, lowerBank_run, same, and_self]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Proofs
