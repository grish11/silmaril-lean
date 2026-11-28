module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Projection Slot)
open Discovery.MemRef.CF (Label Program entryTransition entryTypes evalBody lowerDiamond run)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.DeadStore.SingleUser (readAt)

variable {args : List ValueSort} {cells : Nat}
variable {graph edited : Graph args} {arrival : Slot} {version : Nat}

/-- The admitted Store has one actual user in the diamond and the selected
arm replays the typed single-user bypass. -/
theorem rewrite_checked (accepted : rewrite graph arrival version = some edited) :
    usersOf graph arrival version = [.store (version + 1)] ∧
      ∃ arm, Memory.DeadStore.SingleUser.rewrite (graph.arm (graph.merge.predecessor arrival)) version =
        some arm ∧ edited = replaceArm graph arrival arm :=
  Proofs.rewrite_checked accepted

/-- Retain the exact Region mapping, opposite arm and common suffix. -/
theorem rewrite_shape (accepted : rewrite graph arrival version = some edited) :
    edited.merge = graph.merge ∧ edited.suffix = graph.suffix ∧
      ∀ edge, edge ≠ graph.merge.predecessor arrival → edited.arm edge = graph.arm edge :=
  Proofs.rewrite_shape accepted

/-- The arm exports the same word and heap, and every Load keeps its value. -/
theorem rewrite_arm_observations (accepted : rewrite graph arrival version = some edited)
    (edge : Projection) (input : Tuple (Val cells) args) (initial : Heap cells) :
    (edited.arm edge).denote input initial = (graph.arm edge).denote input initial ∧
      ∀ index, readAt (edited.arm edge) index input PUnit.unit initial =
        readAt (graph.arm edge) index input PUnit.unit initial :=
  Proofs.rewrite_arm_observations accepted edge input initial

/-- The same incoming occurrence latches the same packet. The other
occurrence still observes no publication from this arm. -/
theorem rewrite_latch (accepted : rewrite graph arrival version = some edited)
    (edge : Projection) (slot : Slot) (input : Tuple (Val cells) args) (initial : Heap cells) :
    latch edited.merge slot (publish edge ((edited.arm edge).denote input initial)) =
      latch graph.merge slot (publish edge ((graph.arm edge).denote input initial)) := by
  rw [(rewrite_shape accepted).1, (rewrite_arm_observations accepted edge input initial).1]

/-- The unchanged suffix observes the same Loads from the selected packet. -/
theorem rewrite_suffix_reads (accepted : rewrite graph arrival version = some edited)
    (guard : Bool) (index : Nat) (input : Tuple (Val cells) args) (initial : Heap cells) :
    let selected := (edited.arm (Projection.ofBool guard)).denote input initial
    let original := (graph.arm (Projection.ofBool guard)).denote input initial
    readAt edited.suffix index (.cons selected.1 input) PUnit.unit selected.2 =
      readAt graph.suffix index (.cons original.1 input) PUnit.unit original.2 := by
  dsimp only
  rw [(rewrite_shape accepted).2.1, (rewrite_arm_observations accepted (Projection.ofBool guard) input initial).1]

theorem rewrite_denote (accepted : rewrite graph arrival version = some edited)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) :
    edited.denote guard input initial = graph.denote guard input initial :=
  Proofs.rewrite_denote accepted guard input initial

theorem rewrite_returns_iff (accepted : rewrite graph arrival version = some edited)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) (word : Word) (final : Heap cells) :
    edited.Returns guard input initial word final ↔ graph.Returns guard input initial word final := by
  rw [edited.returns_iff_denote, graph.returns_iff_denote, rewrite_denote accepted]

/-- The emitted entry transfers to the same slot, each arm sends the
same typed jump packet and full buffer to the join, and the CFG result
agrees for either guard at every CF budget. -/
theorem lower_observations {program : Program cells args}
    (emitted : lower cells graph arrival version = some program)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let original := lowerDiamond cells graph none
    entryTransition program input guard initial = entryTransition original input guard initial ∧
      (∀ (slot : Slot) (env : Env entryTypes),
        Block.eval (evalBody input) (program.block (Label.arm slot)) env initial =
          Block.eval (evalBody input) (original.block (Label.arm slot)) env initial) ∧
      run program input guard fuel initial = run original input guard fuel initial :=
  Proofs.lower_observations emitted input guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser
