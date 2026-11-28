module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open DeadStore.Entry.Composition.Static
open Memory.Forwarding.Disjoint (Certificate)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {facts : Certificate args} {input : Tuple (Val cells) args}
variable {entry retained : Memory.Graph args} {store : PrefixStore args} {version : Nat}

/-- Success certifies separation at this input and replays the exact
structural cut using the Load-only tail checker. -/
theorem cut_checked (accepted : cut facts version entry input = some (store, retained)) :
    facts.Valid input ∧ Final.cutWith (Final.LoadTail.checkTail facts) version entry = some (store, retained) :=
  Proofs.cut_checked accepted

/-- Preserve all retained operations and the entry word. Reapplying the
removed write recovers the original whole heap. -/
theorem cut_preserves (accepted : cut facts version entry input = some (store, retained)) (initial : Heap cells) :
    DeletesStores 1 (operations entry) (operations retained) ∧
      entry.denote input initial =
        ((retained.denote input initial).1, (store.table.denote input (retained.denote input initial).2).2) :=
  Proofs.cut_preserves accepted initial

variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {candidate : Candidate args preds}
variable {suffix : Memory.Graph (.word :: args)} {programs : Programs cells args preds}

/-- Replay the valuation-checked cut, the occurrence bank, and the
actual original and optimized switch artifacts. -/
theorem lower_replay (emitted : lower preds fits entry version arm candidate suffix input facts = some programs) :
    ∃ (store : PrefixStore args) (retained : Memory.Graph args) (edited : Bank args preds),
      cut facts version entry input = some (store, retained) ∧
      Finite.check preds store arm candidate input = some edited ∧
      programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some retained) (fun i => edited[i.val]) suffix⟩ :=
  FinalEntry.lowerCut_replay emitted

/-- After a certified entry cut, any refused route blocks emission. -/
theorem lower_eq_none_iff (accepted : cut facts version entry input = some (store, retained)) :
    lower preds fits entry version arm candidate suffix input facts = none ↔
      ∃ arrival, rewriteArm store (arm arrival) (candidate arrival) input = none :=
  FinalEntry.lowerCut_eq_none_iff accepted

/-- The emitted entries keep the chosen scalar result. The switch forwards
the optimized buffer and the corresponding reapplied original buffer at
the same occurrence. -/
theorem lower_entry (emitted : lower preds fits entry version arm candidate suffix input facts = some programs)
    (accepted : cut facts version entry input = some (store, retained))
    (arrival : Occurrence preds) (initial : Buffer cells) :
    DeletesStores 1 (operations entry) (operations retained) ∧
      let exported := observe retained programs.input initial
      let originalBuffer := Buffer.mk (store.table.denote programs.input exported.2.cell).2
      observe entry programs.input initial = (exported.1, originalBuffer) ∧
        entryTransition programs.original programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, originalBuffer) ∧
        entryTransition programs.optimized programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, exported.2) := by
  obtain ⟨order, replay⟩ := cut_preserves accepted initial.cell
  exact ⟨order, FinalEntry.lowerCut_entry emitted accepted arrival initial replay⟩

/-- The two switch CFGs reach the same slot, deliver exactly the same join
packet, and return the native word and whole buffer at every common fuel. -/
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
  FinalEntry.lowerCut_observations emitted arrival fuel initial fun _ _ accepted => by
    have replay := (cut_preserves accepted initial.cell).2
    have heap := congrArg Prod.snd replay
    exact heap

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail
