module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Proofs

open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes)
open SeaOfNodes.Loop (Incoming)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Frame)
open Silmaril.MLIR.CF.Ordered (Block runBlock)
open Silmaril.MLIR.MemRef (Buffer)
open Loop.MLIR.MemRef (observeActivation lowerActivation observeActivation_eq_step)
open Loop.MLIR.MemRef.CF (resultTypes)

variable {cells : Nat} {args : List ValueSort}

private def liftFrame : Frame Loop.MLIR.MemRef.CF.Label → Frame Label
  | ⟨.header, _⟩ => ⟨.header, arrivalEnv .backedge⟩
  | ⟨.exit, values⟩ => ⟨.exit, values⟩

private theorem header_reframe (graph : Graph args) (input : Tuple (Val cells) args)
    (arrival : Incoming) (heap : Heap cells) :
    Block.eval (evalBody graph input) ((lower cells graph).block .header) (arrivalEnv arrival) ⟨heap⟩ =
      let (result, final) := Block.eval (Loop.MLIR.MemRef.CF.evalBody (graph.operands input arrival))
        ((Loop.MLIR.MemRef.CF.lower cells graph.activation).block .header) .nil ⟨heap⟩
      (result.map liftFrame id, final) := by
  let code := lowerActivation cells graph.activation
  have reframe (values : Env (Silmaril.MLIR.Pure.i1 :: resultTypes)) :
      ((lower cells graph).block .header).terminator.eval
          (.cons (values.get .here) (.cons 1 (.cons (values.get (.there .here)) .nil))) =
        ((((Loop.MLIR.MemRef.CF.lower cells graph.activation).block .header).terminator.eval values)
          |>.map liftFrame id) := by
    change Sum.inl (if (values.get .here).getLsbD 0 then (⟨Label.header, arrivalEnv .backedge⟩ : Frame Label)
      else ⟨Label.exit, .cons (values.get (.there .here)) .nil⟩) =
      (Sum.inl (if (values.get .here).getLsbD 0 then
        (⟨Loop.MLIR.MemRef.CF.Label.header, .nil⟩ : Frame Loop.MLIR.MemRef.CF.Label)
        else ⟨Loop.MLIR.MemRef.CF.Label.exit, .cons (values.get (.there .here)) .nil⟩)).map liftFrame id
    split <;> rfl
  let decode (env : Env headerTypes) :=
    if (env.get .here).getLsbD 0 then Incoming.backedge else Incoming.entry
  let evaluate (inc : Incoming) :=
    Loop.MLIR.MemRef.CF.evalBody (graph.operands input inc) (.activation code) .nil ⟨heap⟩
  have decoded : decode (arrivalEnv arrival) = arrival := by cases arrival <;> rfl
  change (let (values, final) := evaluate (decode (arrivalEnv arrival))
    (((lower cells graph).block .header).terminator.eval
      (.cons (values.get .here) (.cons 1 (.cons (values.get (.there .here)) .nil))), final)) =
    (let (values, final) := evaluate arrival
    ((((Loop.MLIR.MemRef.CF.lower cells graph.activation).block .header).terminator.eval values)
      |>.map liftFrame id, final))
  rw [decoded]
  rcases evaluate arrival with ⟨values, final⟩
  exact congrArg (fun result => (result, final)) (reframe values)

theorem header_transition (graph : Graph args) (input : Tuple (Val cells) args)
    (arrival : Incoming) (heap : Heap cells) :
    Block.eval (evalBody graph input) ((lower cells graph).block .header) (arrivalEnv arrival) ⟨heap⟩ =
      match graph.step input arrival heap with
      | .inl (word, final) => (.inl ⟨Label.exit, .cons word .nil⟩, ⟨final⟩)
      | .inr next => (.inl ⟨Label.header, arrivalEnv .backedge⟩, ⟨next⟩) := by
  rw [header_reframe, Loop.MLIR.MemRef.CF.header_transition, observeActivation_eq_step]
  change (let (result, final) : (Frame Loop.MLIR.MemRef.CF.Label ⊕ Env resultTypes) × Buffer cells :=
    match (graph.step input arrival heap).map (fun result => (result.1, Buffer.mk result.2)) Buffer.mk with
    | .inl (word, final) =>
      (Sum.inl ⟨Loop.MLIR.MemRef.CF.Label.exit, .cons word .nil⟩, final)
    | .inr next =>
      (Sum.inl ⟨Loop.MLIR.MemRef.CF.Label.header, .nil⟩, next)
    (result.map liftFrame id, final)) = _
  rcases graph.step input arrival heap with ⟨word, final⟩ | next <;> rfl

theorem petri_activation_iff_header (graph : Graph args) (input : Tuple (Val cells) args)
    (arrival : Incoming) (heap next : Heap cells) (restart : Bool) :
    Finishes (thetaRuntime cells) graph.activation.activation
        (Memory.encodeInput heap (graph.operands input arrival))
        (.cons ⟨if restart then 1 else 0⟩ (Memory.encodeInput next (graph.operands input arrival))) ↔
      Block.eval (evalBody graph input) ((lower cells graph).block .header)
          (arrivalEnv arrival) ⟨heap⟩ =
        (.inl (if restart then ⟨Label.header, arrivalEnv .backedge⟩
          else ⟨Label.exit, .cons (graph.activation.stopWord (graph.operands input arrival)) .nil⟩),
          ⟨next⟩) := by
  rw [Loop.Institution.Lowering.Backends.petri_activation_iff_memref_header, header_reframe]
  let unlift : Frame Label → Frame Loop.MLIR.MemRef.CF.Label
    | ⟨.header, _⟩ => ⟨.header, .nil⟩
    | ⟨.exit, values⟩ => ⟨.exit, values⟩
  have inverse : Function.LeftInverse unlift liftFrame := by
    intro frame
    rcases frame with ⟨label, values⟩
    cases label with
    | header => cases values; rfl
    | exit => rfl
  let lift : (Frame Loop.MLIR.MemRef.CF.Label ⊕ Env resultTypes) × Buffer cells → _
    | (result, final) => (result.map liftFrame id, final)
  let restore (state : (Frame Label ⊕ Env resultTypes) × Buffer cells) :=
    (state.1.map unlift id, state.2)
  have injective : Function.Injective lift :=
    (show Function.LeftInverse restore lift from by
      rintro ⟨frame | result, buffer⟩
      · exact congrArg (fun frame => (Sum.inl frame, buffer)) (inverse frame)
      · rfl).injective
  let baseline := Block.eval (Loop.MLIR.MemRef.CF.evalBody (graph.operands input arrival))
    ((Loop.MLIR.MemRef.CF.lower cells graph.activation).block .header) .nil ⟨heap⟩
  change baseline = _ ↔ lift baseline = _
  rw [← injective.eq_iff]
  cases restart <;> rfl

private def fromHeader (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (arrival : Incoming) (heap : Heap cells) : Option (Word × Buffer cells) :=
  let cfg := lower cells graph
  let (result, final) := runBlock cfg.block (Block.eval (evalBody graph input))
    .nil fuel (cfg.block .header) (arrivalEnv arrival) ⟨heap⟩
  result.map fun values => (values.get .here, final)

private theorem fromHeader_succ (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (arrival : Incoming) (heap : Heap cells) :
    fromHeader graph input (fuel + 1) arrival heap =
      match graph.step input arrival heap with
      | .inl (word, final) => if fuel = 0 then none else some (word, ⟨final⟩)
      | .inr next => fromHeader graph input fuel .backedge next := by
  let cfg := lower cells graph
  let eval {scope} (block : Block (Body cells args) Label scope resultTypes) (env : Env scope) :=
    Block.eval (evalBody graph input) block env
  change (let (outcome, final) := eval (cfg.block .header) (arrivalEnv arrival) ⟨heap⟩
    let (result, final) : Option (Env resultTypes) × Buffer cells := match outcome with
      | .inl frame => runBlock cfg.block eval .nil fuel (cfg.block frame.label) (frame.args.append .nil) final
      | .inr result => (some result, final)
    result.map fun (values : Env resultTypes) => (values.get .here, final)) = _
  rw [show eval (cfg.block .header) (arrivalEnv arrival) ⟨heap⟩ = _ from
    header_transition graph input arrival heap]
  rcases graph.step input arrival heap with ⟨word, final⟩ | next
  · cases fuel <;> rfl
  · rfl

private theorem fromHeader_one (graph : Graph args) (input : Tuple (Val cells) args)
    (arrival : Incoming) (heap : Heap cells) : fromHeader graph input 1 arrival heap = none := by
  rw [fromHeader_succ]
  rcases graph.step input arrival heap with ⟨word, final⟩ | next <;> rfl

private theorem fromHeader_eq (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (arrival : Incoming) (heap : Heap cells) :
    fromHeader graph input (budget + 2) arrival heap =
      (graph.evalWithin input budget arrival heap).map (fun (word, final) => (word, Buffer.mk final)) := by
  induction budget generalizing arrival heap with
  | zero =>
    rw [fromHeader_succ, Graph.evalWithin]
    rcases graph.step input arrival heap with ⟨word, final⟩ | next
    · rfl
    · exact fromHeader_one graph input .backedge next
  | succ budget ih =>
    rw [show budget + 1 + 2 = (budget + 2) + 1 by rfl, fromHeader_succ, Graph.evalWithin]
    rcases graph.step input arrival heap with ⟨word, final⟩ | next
    · rfl
    · exact ih .backedge next

theorem run_eq_evalWithin (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (heap : Heap cells) :
    run graph input budget ⟨heap⟩ =
      (graph.evalWithin input budget .entry heap).map (fun (word, final) => (word, Buffer.mk final)) :=
  fromHeader_eq graph input budget .entry heap

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Proofs
