module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

/-- The actual switch hits the case for the encoded occurrence slot. -/
theorem dispatch_selector (fits : Fits preds) (arrival : Occurrence preds) :
    (dispatch preds fits).select (selectorEnv preds fits arrival) = armEdge preds arrival :=
  Proofs.dispatch_selector fits arrival

variable (fits : Fits preds) (entry : Option (Memory.Graph args))
variable (arm : Occurrence preds → Memory.Graph args) (suffix : Memory.Graph (.word :: args))
variable (input : Tuple (Val cells) args) (arrival : Occurrence preds) (initial : Buffer cells)

/-- The emitted entry selects the original occurrence and forwards its
full post-entry buffer to that arm. -/
theorem lowerBank_entry :
    entryTransition (lowerBank preds fits cells entry arm suffix) input arrival initial =
      (.inl ⟨.arm arrival, .nil⟩,
        ⟨match entry with
          | none => initial.cell
          | some body => (body.denote input initial.cell).2⟩) :=
  Proofs.lowerBank_entry fits entry arm suffix input arrival initial

/-- The selected arm's actual jump carries its word and complete buffer. -/
theorem lowerBank_arm :
    armTransition (lowerBank preds fits cells entry arm suffix) input arrival initial =
      let packet := observe (arm arrival) input initial
      (.inl ⟨.join, .cons packet.1 .nil⟩, packet.2) :=
  Proofs.lowerBank_arm fits entry arm suffix input arrival initial

/-- Three block ticks execute dispatch, the selected arm and the join. -/
theorem lowerBank_run (fuel : Nat) :
    run (lowerBank preds fits cells entry arm suffix) input arrival fuel initial =
      if fuel < 3 then none else
        let entered := match entry with
          | none => initial.cell
          | some body => (body.denote input initial.cell).2
        let packet := (arm arrival).denote input entered
        let result := suffix.denote (.cons packet.1 input) packet.2
        some (result.1, Buffer.mk result.2) :=
  Proofs.lowerBank_run fits entry arm suffix input arrival initial fuel

variable {fits arm suffix input}
variable {store : PrefixStore args} {candidate : Candidate args preds} {programs : Programs cells args preds}

/-- A refused occurrence prevents emission of the checked pair. -/
theorem lower_eq_none_iff :
    lower preds fits store arm candidate suffix input = none ↔
      ∃ arrival, rewriteArm store (arm arrival) (candidate arrival) input = none := by
  rw [← Finite.check_eq_none_iff]
  cases checked : check preds store arm candidate input <;> simp [lower, checked]

/-- For each admitted selector, both emitted CFGs take its exact slot,
send the same join frame and buffer, and agree at every return budget. -/
theorem lower_observations (accepted : lower preds fits store arm candidate suffix input = some programs)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial :=
  Proofs.lower_observations accepted arrival fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF
