module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Proofs

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Projection Slot)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Frame)
open Silmaril.MLIR.CF.Ordered (Block Cfg runBlock)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)
open SeaOfNodes.Memory.MLIR.MemRef renaming lower → lowerMemory

variable {cells : Nat} {args : List ValueSort}

private theorem entry_eval (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (guard : Bool) (initial : Buffer cells) :
    Block.eval (evalBody input) (lowerDiamond cells graph entryBody).entry
        (.cons (BitVec.ofBool guard) .nil) initial =
      (.inl ⟨.arm (graph.merge.slot (Projection.ofBool guard)), .nil⟩,
        enter (entryBody.map (lowerMemory cells)) input initial) := by
  change ((Sum.inl (if (BitVec.ofBool guard).getLsbD 0 then
      (⟨.arm (graph.merge.slot .onTrue), .nil⟩ : Frame Label)
    else ⟨.arm (graph.merge.slot .onFalse), .nil⟩) : Frame Label ⊕ Env resultTypes),
    enter (entryBody.map (lowerMemory cells)) input initial) = _
  cases guard <;> simp [Projection.ofBool]

private theorem arm_eval (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (arrival : Slot) (env : Env entryTypes) (initial : Buffer cells) :
    Block.eval (evalBody input) ((lowerDiamond cells graph entryBody).block (Label.arm arrival)) env initial =
      let selected := observe (graph.arm (graph.merge.predecessor arrival)) input initial
      (.inl ⟨.join, .cons selected.1 .nil⟩, selected.2) := rfl

private theorem join_eval (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (word : Word) (env : Env entryTypes) (initial : Buffer cells) :
    Block.eval (evalBody input) ((lowerDiamond cells graph entryBody).block Label.join)
      (.cons word env) initial =
      let result := observe graph.suffix (.cons word input) initial
      (.inr (.cons result.1 .nil), result.2) := rfl

private theorem bind_state {α β : Type} (first : StateM (Buffer cells) α)
    (next : α → StateM (Buffer cells) β) (initial : Buffer cells) :
    (first >>= next) initial = next (first initial).1 (first initial).2 := by
  change (do let (value, buffer) ← first initial; next value buffer) = _
  cases first initial
  rfl

private theorem run_next (program : Program cells args) (input : Tuple (Val cells) args)
    (entry : Env entryTypes) (fuel : Nat) {scope : List Width}
    {block : Block (Body cells args) Label scope resultTypes} {env : Env scope}
    {initial next : Buffer cells} {frame : Frame Label}
    (step : Block.eval (evalBody input) block env initial = (.inl frame, next)) :
    runBlock program.block (Block.eval (evalBody input)) entry (fuel + 1) block env initial =
      runBlock program.block (Block.eval (evalBody input)) entry fuel
        (program.block frame.label) (frame.args.append entry) next := by
  rw [runBlock, bind_state, step]

private theorem run_ret (program : Program cells args) (input : Tuple (Val cells) args)
    (entry : Env entryTypes) (fuel : Nat) {scope : List Width}
    {block : Block (Body cells args) Label scope resultTypes} {env : Env scope}
    {initial final : Buffer cells} {values : Env resultTypes}
    (step : Block.eval (evalBody input) block env initial = (.inr values, final)) :
    runBlock program.block (Block.eval (evalBody input)) entry (fuel + 1) block env initial =
      (some values, final) := by
  rw [runBlock, bind_state, step]
  rfl

private theorem run_blocks (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    run (lowerDiamond cells graph entryBody) input guard fuel initial =
      if fuel < 3 then none else
        let entered := enter (entryBody.map (lowerMemory cells)) input initial
        let arm := graph.arm (graph.merge.predecessor (graph.merge.slot (Projection.ofBool guard)))
        let selected := observe arm input entered
        some (observe graph.suffix (.cons selected.1 input) selected.2) := by
  unfold run Cfg.run
  rcases fuel with _ | fuel
  · rfl
  let program := lowerDiamond cells graph entryBody
  let entry : Env entryTypes := .cons (BitVec.ofBool guard) .nil
  rw [run_next program input entry fuel (entry_eval graph entryBody input guard initial)]
  rcases fuel with _ | fuel
  · rfl
  let arrival := graph.merge.slot (Projection.ofBool guard)
  let entered := enter (entryBody.map (lowerMemory cells)) input initial
  erw [run_next program input entry fuel (arm_eval graph entryBody input arrival entry entered)]
  rcases fuel with _ | fuel
  · rfl
  let selected := observe (graph.arm (graph.merge.predecessor arrival)) input entered
  erw [run_ret program input entry fuel (join_eval graph entryBody input selected.1 entry selected.2)]
  exact (ite_eq_right (by omega : ¬ (fuel + 1 + 1 + 1 < 3))).symm

private theorem enter_lower (entryBody : Option (Memory.Graph args)) (input : Tuple (Val cells) args)
    (initial : Buffer cells) :
    enter (entryBody.map (lowerMemory cells)) input initial =
      ⟨match entryBody with
        | none => initial.cell
        | some graph => (graph.denote input initial.cell).2⟩ := by
  cases entryBody with
  | none => rfl
  | some graph =>
    change (observe graph input initial).2 = _
    rw [lower_run]

theorem lowerDiamond_entryTransition (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (guard : Bool) (initial : Buffer cells) :
    entryTransition (lowerDiamond cells graph entryBody) input guard initial =
      (.inl ⟨.arm (graph.merge.slot (Projection.ofBool guard)), .nil⟩,
        ⟨match entryBody with
          | none => initial.cell
          | some body => (body.denote input initial.cell).2⟩) := by
  unfold entryTransition
  rw [entry_eval, enter_lower]
  rfl

theorem lowerDiamond_run (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    run (lowerDiamond cells graph entryBody) input guard fuel initial =
      if fuel < 3 then none else
        let entered := match entryBody with
          | none => initial.cell
          | some graph => (graph.denote input initial.cell).2
        let result := graph.denote guard input entered
        some (result.1, Buffer.mk result.2) := by
  rw [run_blocks]
  split
  · rfl
  · simp only [enter_lower, graph.merge.predecessor_slot]
    rw [lower_run, lower_run]
    rfl

theorem lower_runs {source : Prefixed args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (accepted : lower source input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := source.denote guard input initial.cell
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  obtain ⟨result, discovered, packed⟩ := Option.bind_eq_some_iff.mp accepted
  cases Option.some.inj packed
  constructor
  · exact lowerDiamond_run source.diamond (some source.store.table) input guard fuel initial
  · exact (lowerDiamond_run result.graph none input guard fuel initial).trans
      (congrArg (fun value : Word × Heap cells =>
        if fuel < 3 then none else some (value.1, Buffer.mk value.2))
        (Discovery.rewrite_denote input discovered guard initial.cell))

private theorem rewrite_merge {source : Prefixed args} {result : Discovery.Result args}
    (input : Tuple (Val cells) args) (success : Discovery.rewrite source input = some result) :
    result.graph.merge = source.diamond.merge := by
  have checked := (Discovery.rewrite_checked input success).2
  obtain ⟨first, _, tail⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨second, _, packed⟩ := Option.bind_eq_some_iff.mp tail
  have merged := congrArg (fun graph : Graph args => graph.merge) (Option.some.inj packed)
  exact merged.symm

private theorem lowerDiamond_entry (graph : Graph args) (entryBody : Option (Memory.Graph args))
    (input : Tuple (Val cells) args) (guard : Bool) (initial : Buffer cells) :
    entryDestination (lowerDiamond cells graph entryBody) input guard initial =
      .inl ⟨.arm (graph.merge.slot (Projection.ofBool guard)), .nil⟩ := by
  exact congrArg Prod.fst (entry_eval graph entryBody input guard initial)

theorem lower_entry_slots {source : Prefixed args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (accepted : lower source input = some programs)
    (guard : Bool) (initial : Buffer cells) :
    let destination : Silmaril.MLIR.CF.Frame Label :=
      ⟨.arm (source.diamond.merge.slot (Projection.ofBool guard)), .nil⟩
    entryDestination programs.original programs.input guard initial = .inl destination ∧
      entryDestination programs.optimized programs.input guard initial = .inl destination := by
  obtain ⟨result, discovered, packed⟩ := Option.bind_eq_some_iff.mp accepted
  cases Option.some.inj packed
  constructor
  · exact lowerDiamond_entry source.diamond (some source.store.table) input guard initial
  · exact (lowerDiamond_entry result.graph none input guard initial).trans
      (by rw [rewrite_merge input discovered])

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Proofs
