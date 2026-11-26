module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Proofs

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Frame)
open Silmaril.MLIR.CF.Ordered (runBlock)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (enter resultTypes)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)
open SeaOfNodes.Memory.MLIR.MemRef renaming lower → lowerMemory

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

theorem dispatch_selector (fits : Fits preds) (arrival : Occurrence preds) :
    (dispatch preds fits).select (selectorEnv preds fits arrival) = armEdge preds arrival := by
  let matchesSelector := fun position : Occurrence preds =>
    selectorBits preds fits position == selectorBits preds fits arrival
  have located : (List.finRange (preds.rest.length + 1)).find? matchesSelector = some arrival := by
    cases found : (List.finRange (preds.rest.length + 1)).find? matchesSelector with
    | none =>
      exact False.elim ((List.find?_eq_none.mp found) arrival (List.mem_finRange _) (by simp [matchesSelector]))
    | some position =>
      have matched := List.find?_some found
      have same : position = arrival :=
        Fin.ext (by simpa [matchesSelector, selectorBits] using congrArg BitVec.toNat (beq_iff_eq.mp matched))
      rw [same]
  dsimp only [matchesSelector] at located
  simp only [Silmaril.MLIR.CF.SwitchAssert.Switch.select, dispatch, selectorEnv, Env.get, List.find?_map,
    Function.comp_def, switchCase]
  erw [located]
  rfl

private theorem enter_lower (entry : Option (Memory.Graph args)) (input : Tuple (Val cells) args)
    (initial : Buffer cells) :
    enter (entry.map (lowerMemory cells)) input initial =
      ⟨match entry with
        | none => initial.cell
        | some body => (body.denote input initial.cell).2⟩ := by
  cases entry with
  | none => rfl
  | some body =>
    change (observe body input initial).2 = _
    rw [lower_run]

variable (fits : Fits preds) (entry : Option (Memory.Graph args))
variable (arm : Occurrence preds → Memory.Graph args) (suffix : Memory.Graph (.word :: args))
variable (input : Tuple (Val cells) args) (arrival : Occurrence preds) (initial : Buffer cells)

theorem lowerBank_entry :
    entryTransition (lowerBank preds fits cells entry arm suffix) input arrival initial =
      (.inl ⟨.arm arrival, .nil⟩,
        ⟨match entry with
          | none => initial.cell
          | some body => (body.denote input initial.cell).2⟩) := by
  change (Sum.inl (β := Env resultTypes) (((dispatch preds fits).select (selectorEnv preds fits arrival)).eval
      (selectorEnv preds fits arrival)),
    enter (entry.map (lowerMemory cells)) input initial) = _
  rw [dispatch_selector, enter_lower]
  rfl

theorem lowerBank_arm :
    armTransition (lowerBank preds fits cells entry arm suffix) input arrival initial =
      let packet := observe (arm arrival) input initial
      (.inl ⟨.join, .cons packet.1 .nil⟩, packet.2) := by
  rfl

private theorem join_eval (word : Word) :
    eval input (.block ((lowerBank preds fits cells entry arm suffix).block Label.join))
      (.cons word (selectorEnv preds fits arrival)) initial =
      let result := observe suffix (.cons word input) initial
      (.inr (.cons result.1 .nil), result.2) := by
  rfl

private theorem bind_state {α β : Type} (first : StateM (Buffer cells) α)
    (next : α → StateM (Buffer cells) β) (initial : Buffer cells) :
    (first >>= next) initial = next (first initial).1 (first initial).2 := by
  change (do let (value, buffer) ← first initial; next value buffer) = _
  cases first initial
  rfl

private theorem advance (program : Program cells args preds) (input : Tuple (Val cells) args)
    (env : Env inputTypes) (fuel : Nat) {scope : List Width}
    {block : Scheduled cells args preds scope} {current : Env scope}
    {initial next : Buffer cells} {frame : Frame (Label preds)}
    (step : eval input block current initial = (.inl frame, next)) :
    runBlock (fun label => .block (program.block label)) (eval input) env (fuel + 1) block current initial =
      runBlock (fun label => .block (program.block label)) (eval input) env fuel
        (.block (program.block frame.label)) (frame.args.append env) next := by
  rw [runBlock, bind_state, step]

private theorem finish (program : Program cells args preds) (input : Tuple (Val cells) args)
    (env : Env inputTypes) (fuel : Nat) {scope : List Width}
    {block : Scheduled cells args preds scope} {current : Env scope}
    {initial final : Buffer cells} {words : Env resultTypes}
    (step : eval input block current initial = (.inr words, final)) :
    runBlock (fun label => .block (program.block label)) (eval input) env (fuel + 1) block current initial =
      (some words, final) := by
  rw [runBlock, bind_state, step]
  rfl

theorem lowerBank_run (fuel : Nat) :
    run (lowerBank preds fits cells entry arm suffix) input arrival fuel initial =
      if fuel < 3 then none else
        let entered := match entry with
          | none => initial.cell
          | some body => (body.denote input initial.cell).2
        let packet := (arm arrival).denote input entered
        let result := suffix.denote (.cons packet.1 input) packet.2
        some (result.1, Buffer.mk result.2) := by
  unfold run
  rcases fuel with _ | fuel
  · rfl
  let program := lowerBank preds fits cells entry arm suffix
  let env := selectorEnv preds fits arrival
  let entered : Buffer cells := ⟨match entry with
    | none => initial.cell
    | some body => (body.denote input initial.cell).2⟩
  have step : eval input (.entry program.entry) env initial = (.inl ⟨.arm arrival, .nil⟩, entered) :=
    lowerBank_entry fits entry arm suffix input arrival initial
  let observeResult := fun (result : Option (Env resultTypes) × Buffer cells) =>
    result.1.map fun words => (words.get .here, result.2)
  change observeResult (runBlock (fun label => .block (program.block label)) (eval input) env
    (fuel + 1) (.entry program.entry) env initial) = _
  erw [advance program input env fuel step]
  rcases fuel with _ | fuel
  · rfl
  let packet := observe (arm arrival) input entered
  have stepArm : eval input (.block (program.block (.arm arrival))) env entered =
      (.inl ⟨.join, .cons packet.1 .nil⟩, packet.2) :=
    lowerBank_arm fits entry arm suffix input arrival entered
  erw [advance program input env fuel stepArm]
  rcases fuel with _ | fuel
  · rfl
  erw [finish program input env fuel (join_eval fits entry arm suffix input arrival packet.2 packet.1)]
  simp only [ite_eq_right (by omega : ¬ fuel + 1 + 1 + 1 < 3), lower_run, packet]
  rfl

variable {fits entry arm suffix input arrival initial}
variable {store : PrefixStore args} {candidate : Candidate args preds} {programs : Programs cells args preds}

theorem lower_observations (accepted : lower preds fits store arm candidate suffix input = some programs)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial := by
  obtain ⟨edited, checked, packed⟩ := Option.bind_eq_some_iff.mp accepted
  cases Option.some.inj packed
  have same := (Finite.check_observations checked arrival initial.cell).1
  refine ⟨congrArg Prod.fst (lowerBank_entry fits _ arm suffix input arrival initial),
    congrArg Prod.fst (lowerBank_entry fits _ _ suffix input arrival initial), ?_, ?_⟩
  · simp only [lowerBank_entry, lowerBank_arm, lower_run]
    exact congrArg (fun packet : Word × Heap cells =>
      (Sum.inl (β := Env resultTypes) (⟨.join, .cons packet.1 .nil⟩ : Frame (Label preds)),
        Buffer.mk packet.2)) same
  · rw [lowerBank_run, lowerBank_run]
    dsimp only
    rw [same]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Proofs
