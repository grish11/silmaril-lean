module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Projection Slot)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {cells : Nat} {args : List ValueSort}

/-- The emitted entry keeps the guard's Region occurrence and forwards the
entire buffer produced by the optional entry body at this scalar input. -/
theorem lowerDiamond_entryTransition (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (guard : Bool) (initial : Buffer cells) :
    entryTransition (lowerDiamond cells graph entryBody) input guard initial =
      (.inl ⟨.arm (graph.merge.slot (Projection.ofBool guard)), .nil⟩,
        ⟨match entryBody with
          | none => initial.cell
          | some body => (body.denote input initial.cell).2⟩) :=
  Proofs.lowerDiamond_entryTransition graph entryBody input guard initial

/-- The actual arm block passes its word and complete buffer to the join
from the predecessor designated by this Region occurrence. -/
theorem lowerDiamond_arm_eval (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (arrival : Slot) (env : Env entryTypes) (initial : Buffer cells) :
    Block.eval (evalBody input) ((lowerDiamond cells graph entryBody).block (Label.arm arrival)) env initial =
      let selected := observe (graph.arm (graph.merge.predecessor arrival)) input initial
      (.inl ⟨.join, .cons selected.1 .nil⟩, selected.2) :=
  Proofs.arm_eval graph entryBody input arrival env initial

/-- The ordered diamond runs on the heap supplied by the optional entry body. -/
theorem lowerDiamond_run (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    run (lowerDiamond cells graph entryBody) input guard fuel initial =
      if fuel < 3 then none else
        let entered := match entryBody with
          | none => initial.cell
          | some body => (body.denote input initial.cell).2
        let result := graph.denote guard input entered
        some (result.1, Buffer.mk result.2) :=
  Proofs.lowerDiamond_run graph entryBody input guard fuel initial

/-- Running with an entry body agrees on the return observation with
seeding the bare diamond from the emitted entry's buffer. Both runs use
the same typed scalar input and predicate. -/
theorem lowerDiamond_run_seeded (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let original := lowerDiamond cells graph entryBody
    let entered := (entryTransition original input guard initial).2
    run original input guard fuel initial = run (lowerDiamond cells graph none) input guard fuel entered := by
  dsimp only
  rw [lowerDiamond_entryTransition, lowerDiamond_run, lowerDiamond_run]

theorem lower_eq_none_iff (source : Prefixed args) (input : Tuple (Val cells) args) :
    lower source input = none ↔ Discovery.rewrite source input = none := by
  cases checked : Discovery.rewrite source input <;> simp [lower, checked]

/-- Both emitted artifacts take the original incoming Region slot. -/
theorem lower_entry_slots {source : Prefixed args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (accepted : lower source input = some programs)
    (guard : Bool) (initial : Buffer cells) :
    let destination : Silmaril.MLIR.CF.Frame Label :=
      ⟨.arm (source.diamond.merge.slot (Projection.ofBool guard)), .nil⟩
    entryDestination programs.original programs.input guard initial = .inl destination ∧
      entryDestination programs.optimized programs.input guard initial = .inl destination :=
  Proofs.lower_entry_slots input accepted guard initial

/-- Run the actual arm blocks from their respective emitted entry buffers.
At each Region occurrence the jump frame, word and full buffer agree.
With `lower_entry_slots` this gives the packet on the selected route. -/
theorem lower_join_eq {source : Prefixed args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (accepted : lower source input = some programs)
    (guard : Bool) (arrival : Slot) (initial : Buffer cells) :
    let env : Env entryTypes := .cons (BitVec.ofBool guard) .nil
    let before := (entryTransition programs.original programs.input guard initial).2
    let after := (entryTransition programs.optimized programs.input guard initial).2
    Block.eval (evalBody programs.input) (programs.optimized.block (Label.arm arrival)) env after =
      Block.eval (evalBody programs.input) (programs.original.block (Label.arm arrival)) env before :=
  Proofs.lower_join_eq input accepted guard arrival initial

/-- Three block steps reach the return in either artifact. The observation
includes the returned word and every final cell at the checked input. -/
theorem lower_runs {source : Prefixed args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (accepted : lower source input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := source.denote guard input initial.cell
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_runs input accepted guard fuel initial

theorem run_optimized_eq_original {source : Prefixed args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (accepted : lower source input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    run programs.optimized programs.input guard fuel initial =
      run programs.original programs.input guard fuel initial :=
  let both := lower_runs input accepted guard fuel initial
  both.2.trans both.1.symm

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF
