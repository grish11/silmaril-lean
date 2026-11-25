module

public import Silmaril.SSA.MLIR.SCF.LetIter.Defs
public import Silmaril.SSA.MLIR.SCF.LetIter.Behaviour
public import Silmaril.SSA.MLIR.SCF.While

/-! # The typed scalar while fragment at the LetIter boundary

Each typed block is interpreted as one total call at its declared input profile.
The block code is part of the instruction symbol, so two loops with the same
profiles use the same model for a given primitive interpretation and input.
The LetIter controller handles the condition, backedge and parent continuation.
-/

@[expose] public section

namespace Silmaril.MLIR.SCF.LetIter.ScalarWhile

open Arith (Width Env)
open Silmaril.MLIR.Pure (Code Operands OpSignature)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Institution.Observational (Model Observation iterBeh)
open Silmaril.Isotope.LetIter.LocallyNameless (HasType)

variable {Op : OpSignature} {Input Result State Payload : List Width}

/-- The atoms distinguish vectors at the three interfaces, even when their
width lists coincide. -/
inductive Atom (State Payload Result : List Width) where
  | state (values : Env State)
  | payload (values : Env Payload)
  | result (values : Env Result)

/-- Primitive calls for the four individual blocks of the typed while. -/
inductive Call (Op : OpSignature) (Input Result State Payload : List Width) where
  | init (operands : Operands Input State)
  | before (code : Code Op (Condition Payload) (State ++ Input))
  | yield (code : Code Op (Yield State) (Payload ++ Input))
  | parent (code : Code Op (Return Result) (Payload ++ Input))

/-- The interfaces are native base types. -/
inductive Interface where
  | state | payload | result

instance : HasTy (Call Op Input Result State Payload) (Ty Interface) where
  src
    | .init _ => .unit
    | .before _ => .base .state
    | .yield _ | .parent _ => .base .payload
  trg
    | .init _ | .yield _ => .base .state
    | .before _ => .coprod (.base .payload) (.base .payload)
    | .parent _ => .base .result

/-- Interpret a single block. Input vectors are kept in the model because the
native term has already been closed at the chosen enclosing input. -/
def Call.run (evalOp : Pure.Eval Op) (input : Env Input) :
    Call Op Input Result State Payload → Value (Atom State Payload Result) →
      Option (Value (Atom State Payload Result))
  | .init operands, .unit => some (.atom (.state (operands.eval input)))
  | .before code, .atom (.state state) =>
      let tested : Bool × Env Payload := code.eval evalOp Condition.eval (state.append input)
      some (if tested.1 then .inr (.atom (.payload tested.2)) else .inl (.atom (.payload tested.2)))
  | .yield code, .atom (.payload payload) =>
      some (.atom (.state (code.eval evalOp Yield.eval (payload.append input))))
  | .parent code, .atom (.payload payload) =>
      some (.atom (.result (code.eval evalOp Return.eval (payload.append input))))
  | _, _ => none

/-- The scalar evaluator gives a state-free, fault-free primitive model. -/
abbrev model (evalOp : Pure.Eval Op) (input : Env Input) : Model.{0, 0, 0}
    (Call Op Input Result State Payload) 0 where
  α := Atom State Payload Result
  σ := Unit
  instr f arg _ out _ := f.run evalOp input arg = some out
  faults _ _ _ _ := False
  prim _ _ _ := False
  bound i := i.elim0

/-- Expose the four typed scalar regions at one LetIter boundary. -/
def toRegionLoop (loop : While Op Input Result) :
    RegionLoop (Call Op Input Result loop.State loop.Payload) 0 where
  init := .op (.init loop.init) .unit
  condition := .op (.before loop.before) (.bv 0)
  afterRegion := .op (.yield loop.after) (.bv 0)
  parent := .op (.parent loop.cont) (.bv 0)

theorem toRegionLoop_wellTyped (loop : While Op Input Result) :
    (toRegionLoop loop).WellTyped (τ := Ty Interface) .nil .nil (.base .state) (.base .payload) (.base .result) :=
  ⟨.op .unit, .op .newest, .op .newest, .op .newest⟩

/-- Native LetIter observations for this typed scalar realization. -/
def observe (loop : While Op Input Result) (evalOp : Pure.Eval Op) (input : Env Input) :
    Set (Observation (Value (Atom loop.State loop.Payload Result)) Unit) :=
  iterBeh (model evalOp input) (toRegionLoop loop).lower

end Silmaril.MLIR.SCF.LetIter.ScalarWhile
