module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open DeadStore.Entry.Composition.Static
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {entry retained : Memory.Graph args} {store : PrefixStore args} {version : Nat}
variable {arm : Occurrence preds → Memory.Graph args} {candidate : Candidate args preds}
variable {suffix : Memory.Graph (.word :: args)} {input : Tuple (Val cells) args} {programs : Programs cells args preds}
variable {edit : Option (PrefixStore args × Memory.Graph args)}

theorem lowerCut_replay (emitted : lowerCut preds fits entry edit arm candidate suffix input = some programs) :
    ∃ (store : PrefixStore args) (retained : Memory.Graph args) (edited : Bank args preds),
      edit = some (store, retained) ∧
      Finite.check preds store arm candidate input = some edited ∧
      programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some retained) (fun i => edited[i.val]) suffix⟩ :=
  Proofs.lowerCut_replay emitted

theorem lowerCut_eq_none_iff (accepted : edit = some (store, retained)) :
    lowerCut preds fits entry edit arm candidate suffix input = none ↔
      ∃ arrival, rewriteArm store (arm arrival) (candidate arrival) input = none := by
  rw [← Finite.check_eq_none_iff]
  cases checked : Finite.check preds store arm candidate input <;> simp [lowerCut, accepted, checked]

/-- A checked entry replay gives the exact emitted scalar and buffer
relation at the selected switch occurrence. -/
theorem lowerCut_entry (emitted : lowerCut preds fits entry edit arm candidate suffix input = some programs)
    (accepted : edit = some (store, retained)) (arrival : Occurrence preds) (initial : Buffer cells)
    (replay : entry.denote input initial.cell =
      ((retained.denote input initial.cell).1, (store.table.denote input (retained.denote input initial.cell).2).2)) :
    let exported := observe retained programs.input initial
    let originalBuffer := Buffer.mk (store.table.denote programs.input exported.2.cell).2
    observe entry programs.input initial = (exported.1, originalBuffer) ∧
      entryTransition programs.original programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, originalBuffer) ∧
      entryTransition programs.optimized programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, exported.2) :=
  Proofs.lowerCut_entry emitted accepted arrival initial replay

/-- Compose the entry's buffer replay with the checked arm bank and
the common suffix in the actual switch CFGs. -/
theorem lowerCut_observations (emitted : lowerCut preds fits entry edit arm candidate suffix input = some programs)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells)
    (reapply : ∀ (store : PrefixStore args) (retained : Memory.Graph args), edit = some (store, retained) →
      (entry.denote input initial.cell).2 = (store.table.denote input (retained.denote input initial.cell).2).2) :
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
  Proofs.lowerCut_observations emitted arrival fuel initial reapply

/-- Replay the typed entry edit, every checked occurrence, and the exact
two switch CFGs emitted from those tables. -/
theorem lower_replay (emitted : lower preds fits entry version arm candidate suffix input = some programs) :
    ∃ (store : PrefixStore args) (retained : Memory.Graph args) (edited : Bank args preds),
      Final.cut version entry = some (store, retained) ∧
      Finite.check preds store arm candidate input = some edited ∧
      programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some retained) (fun i => edited[i.val]) suffix⟩ :=
  lowerCut_replay emitted

/-- After the entry cut, one refused occurrence prevents emission. -/
theorem lower_eq_none_iff (accepted : Final.cut version entry = some (store, retained)) :
    lower preds fits entry version arm candidate suffix input = none ↔
      ∃ arrival, rewriteArm store (arm arrival) (candidate arrival) input = none :=
  lowerCut_eq_none_iff accepted

/-- The two emitted entries preserve the scalar result and retained
operations. Reapplying the removed write to the optimized entry buffer
recovers the original entry buffer at the same selected occurrence. -/
theorem lower_entry (emitted : lower preds fits entry version arm candidate suffix input = some programs)
    (accepted : Final.cut version entry = some (store, retained))
    (arrival : Occurrence preds) (initial : Buffer cells) :
    DeletesStores 1 (operations entry) (operations retained) ∧
      let exported := observe retained programs.input initial
      let originalBuffer := Buffer.mk (store.table.denote programs.input exported.2.cell).2
      observe entry programs.input initial = (exported.1, originalBuffer) ∧
        entryTransition programs.original programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, originalBuffer) ∧
        entryTransition programs.optimized programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, exported.2) := by
  obtain ⟨order, replay⟩ := Final.cut_preserves input accepted
  exact ⟨order, lowerCut_entry emitted accepted arrival initial (replay PUnit.unit initial.cell)⟩

/-- For every certified slot and initial buffer, the actual emitted arms
send the same join frame, word and entire buffer. Both CFGs return the
native word and full buffer with the same budget. -/
theorem lower_observations (emitted : lower preds fits entry version arm candidate suffix input = some programs)
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
  lowerCut_observations emitted arrival fuel initial fun _ _ accepted => by
    have replay := (Final.cut_preserves input accepted).2 PUnit.unit initial.cell
    have heap := congrArg Prod.snd replay
    exact heap

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry
