module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser.Proofs

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Projection Slot)
open Discovery.MemRef.CF (Label Program entryTransition entryTypes evalBody lowerDiamond lowerDiamond_arm_eval
  lowerDiamond_entryTransition lowerDiamond_run run)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (lower_run)
open Memory.DeadStore.SingleUser (readAt)

variable {args : List ValueSort} {cells : Nat}
variable {graph edited : Graph args} {arrival : Slot} {version : Nat}

theorem rewrite_checked (accepted : rewrite graph arrival version = some edited) :
    usersOf graph arrival version = [.store (version + 1)] ∧
      ∃ arm, Memory.DeadStore.SingleUser.rewrite (graph.arm (graph.merge.predecessor arrival)) version =
        some arm ∧ edited = replaceArm graph arrival arm := by
  obtain ⟨arm, checked, rfl⟩ := Option.map_eq_some_iff.mp accepted
  exact ⟨by simp [usersOf, (Memory.DeadStore.SingleUser.rewrite_checked checked).1], arm, checked, rfl⟩

theorem rewrite_shape (accepted : rewrite graph arrival version = some edited) :
    edited.merge = graph.merge ∧ edited.suffix = graph.suffix ∧
      ∀ edge, edge ≠ graph.merge.predecessor arrival → edited.arm edge = graph.arm edge := by
  obtain ⟨_, _, _, rfl⟩ := rewrite_checked accepted
  exact ⟨rfl, rfl, fun edge other => by simp [replaceArm, other]⟩

theorem rewrite_arm_observations (accepted : rewrite graph arrival version = some edited)
    (edge : Projection) (input : Tuple (Val cells) args) (initial : Heap cells) :
    (edited.arm edge).denote input initial = (graph.arm edge).denote input initial ∧
      ∀ index, readAt (edited.arm edge) index input PUnit.unit initial =
        readAt (graph.arm edge) index input PUnit.unit initial := by
  obtain ⟨_, arm, checked, rfl⟩ := rewrite_checked accepted
  by_cases chosen : edge = graph.merge.predecessor arrival
  · subst edge
    simpa [replaceArm] using And.intro (Memory.DeadStore.SingleUser.rewrite_denote checked input initial)
      (fun index => Memory.DeadStore.SingleUser.rewrite_readAt checked index input initial)
  · simp [replaceArm, chosen]

theorem rewrite_denote (accepted : rewrite graph arrival version = some edited)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) :
    edited.denote guard input initial = graph.denote guard input initial := by
  simp only [Graph.denote, (rewrite_shape accepted).2.1,
    (rewrite_arm_observations accepted (Projection.ofBool guard) input initial).1]

theorem lower_observations {program : Program cells args}
    (emitted : lower cells graph arrival version = some program)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let original := lowerDiamond cells graph none
    entryTransition program input guard initial = entryTransition original input guard initial ∧
      (∀ (slot : Slot) (env : Env entryTypes),
        Block.eval (evalBody input) (program.block (Label.arm slot)) env initial =
          Block.eval (evalBody input) (original.block (Label.arm slot)) env initial) ∧
      run program input guard fuel initial = run original input guard fuel initial := by
  obtain ⟨target, accepted, rfl⟩ := Option.map_eq_some_iff.mp emitted
  have merge := (rewrite_shape accepted).1
  constructor
  · simp only [lowerDiamond_entryTransition, merge]
  constructor
  · intro slot env
    rw [lowerDiamond_arm_eval, lowerDiamond_arm_eval, merge, lower_run, lower_run,
      (rewrite_arm_observations accepted (graph.merge.predecessor slot) input initial.cell).1]
  · rw [lowerDiamond_run, lowerDiamond_run]
    dsimp only
    rw [rewrite_denote accepted guard input initial.cell]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser.Proofs
