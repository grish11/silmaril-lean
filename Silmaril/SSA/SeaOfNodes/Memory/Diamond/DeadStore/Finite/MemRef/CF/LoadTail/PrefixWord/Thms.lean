module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord

open RVSDG (Locals Tuple)
open Memory.Forwarding.Disjoint (Certificate cell)
open Memory.DeadStore (readAt throughLoad)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Quads.CFG.Predecessors sites}
variable {facts : Certificate args} {input : Tuple (Val cells) args} {version : Nat}

/-- The shared prefix computes the original Store operand. Both suffixes
produce the same word, and reapplying exactly that write restores the heap. -/
theorem cut_preserves {past : List (List ValueSort)} {live : Nat}
    {body : Memory.Body args past live} {edit : Cut args past live}
    (accepted : cut facts version body = some edit) (valid : facts.Valid input) :
    DeletesStores 1 (operations body) (operations edit.retained) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let pre := edit.beforeStore.denote input locals initial
        let retained := edit.retained.denote input locals initial
        retained.2 = pre.2 ∧
          body.denote input locals initial = (retained.1, pre.2.write (cell input edit.address) pre.1) :=
  Proofs.cut_preserves accepted valid

/-- Deleting the certified Store preserves every ordered entry Load word,
from the shared prefix through the final suffix. -/
theorem cut_readbacks {past : List (List ValueSort)} {live : Nat}
    {body : Memory.Body args past live} {edit : Cut args past live}
    (accepted : cut facts version body = some edit) (valid : facts.Valid input)
    (locals : Locals (Val cells) past) (initial : Heap cells) (index : Nat) :
    readAt body index input locals initial = readAt edit.retained index input locals initial :=
  Proofs.cut_readbacks accepted valid locals initial index

/-- An admitted arm preserves its ordered readbacks and entire result for
any incoming write word at the nominated cell. -/
theorem checkArm_observations {address : RVSDG.Port args .address} {arm : Memory.Graph args}
    {witness : ArmOverwrite args} (checked : checkArm address arm witness input = true)
    (initial : Heap cells) (word : Word) :
    let written := initial.write (cell input address) word
    arm.denote input initial = arm.denote input written ∧
      ∀ index, Memory.DeadStore.readAt arm index input PUnit.unit initial =
        Memory.DeadStore.readAt arm index input PUnit.unit written :=
  Proofs.checkArm_observations checked initial word

variable {fits : Fits preds} {entry : Memory.Graph args}
variable {arm : Occurrence preds → Memory.Graph args} {candidate : Candidate args preds}
variable {suffix : Memory.Graph (.word :: args)} {programs : Programs cells args preds}

/-- Project the executable result from the enriched entry emission. -/
theorem lower_eq_map_lowerWithEntry :
    lower preds fits entry version arm candidate suffix input facts =
      (lowerWithEntry preds fits entry version arm candidate suffix input facts).map Emission.programs :=
  Proofs.lower_eq_map_lowerWithEntry

/-- The checked native edit and both actual artifacts come from the same
cut and invocation. Each original occurrence passes its own route check. -/
theorem lowerWithEntry_replay {emission : Emission cells args preds}
    (emitted : lowerWithEntry preds fits entry version arm candidate suffix input facts = some emission) :
    cut facts version entry = some emission.edit ∧ facts.Valid input ∧
      (∀ i, checkArm emission.edit.address (arm i) (candidate i) input = true) ∧
      emission.programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some emission.edit.retained) arm suffix⟩ :=
  Proofs.lowerWithEntry_replay emitted

theorem lowerWithEntry_programs {emission : Emission cells args preds}
    (emitted : lowerWithEntry preds fits entry version arm candidate suffix input facts = some emission) :
    lower preds fits entry version arm candidate suffix input facts = some emission.programs := by
  rw [lower_eq_map_lowerWithEntry, emitted]
  rfl

/-- Successful emission uses the checked edit and the original occurrence
bank and continuation. -/
theorem lower_replay (emitted : lower preds fits entry version arm candidate suffix input facts = some programs) :
    ∃ edit, cut facts version entry = some edit ∧ facts.Valid input ∧
      (∀ i, checkArm edit.address (arm i) (candidate i) input = true) ∧
      programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some edit.retained) arm suffix⟩ :=
  Proofs.lower_replay emitted

/-- After successful switch emission, the original and retained entries
give the same word when probed at any Load via the existing MemRef emitter. -/
theorem lower_readbacks (emitted : lower preds fits entry version arm candidate suffix input facts = some programs)
    {edit : Cut args [] 0} (accepted : cut facts version entry = some edit)
    (index : Nat) (initial : Buffer cells) :
    let probe := fun (graph : Memory.Graph args) => (throughLoad graph index).map fun block =>
      (observe block programs.input initial).1
    probe entry = probe edit.retained :=
  Proofs.lower_readbacks emitted accepted index initial

/-- The emitted entry keeps the suffix word and transfers the exact buffer
to the selected occurrence, with only the nominated write removed. -/
theorem lower_entry (emitted : lower preds fits entry version arm candidate suffix input facts = some programs)
    {edit : Cut args [] 0} (accepted : cut facts version entry = some edit)
    (arrival : Occurrence preds) (initial : Buffer cells) :
    DeletesStores 1 (operations entry) (operations edit.retained) ∧
    let pre := observe edit.beforeStore programs.input initial
    let retained := observe edit.retained programs.input initial
    let restored := Buffer.mk (Heap.write pre.2.cell (cell programs.input edit.address) pre.1)
    retained.2 = pre.2 ∧ observe entry programs.input initial = (retained.1, restored) ∧
      entryTransition programs.original programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, restored) ∧
      entryTransition programs.optimized programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, retained.2) :=
  Proofs.lower_entry emitted accepted arrival initial

/-- The emitted CFGs carry the same exact selected join packet and agree
on the returned word and full buffer at every common CF budget. -/
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
      run programs.optimized programs.input arrival fuel initial = expected :=
  Proofs.lower_observations emitted arrival fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord
