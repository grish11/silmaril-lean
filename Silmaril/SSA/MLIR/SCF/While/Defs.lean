module

public import Silmaril.SSA.MLIR.CF.Basic

/-! A single pure `scf.while` and its lowering to four CFG blocks. -/

@[expose] public section

namespace Silmaril.MLIR.SCF

open Arith (Width Var Env)
open Silmaril.MLIR.Pure (Code Eval Operands OpSignature i1)

/-- `scf.condition` forwards the same payload to the after region on true and
to the enclosing continuation on false. -/
inductive Condition (Payload Γ : List Width) where
  | condition (test : Var Γ i1) (values : Operands Γ Payload)

/-- `scf.yield` supplies the next before-region arguments. -/
inductive Yield (State Γ : List Width) where
  | yield (values : Operands Γ State)

/-- Return from the parent continuation to the fragment boundary. -/
inductive Return (Result Γ : List Width) where
  | ret (values : Operands Γ Result)

/-- The input is the parent scope immediately before the while. Region arguments
and while results are in front of this scope. Region locals cannot escape
except through their terminator operands. -/
structure While (Op : OpSignature) (Input Result : List Width) where
  State : List Width
  Payload : List Width
  init : Operands Input State
  before : Code Op (Condition Payload) (State ++ Input)
  after : Code Op (Yield State) (Payload ++ Input)
  cont : Code Op (Return Result) (Payload ++ Input)

variable {Op : OpSignature} {Input Result Γ State Payload : List Width}

def Condition.eval (term : Condition Payload Γ) (env : Env Γ) : Bool × Env Payload :=
  match term with
  | .condition test values => ((env.get test).getLsbD 0, values.eval env)

def Yield.eval (term : Yield State Γ) (env : Env Γ) : Env State :=
  match term with
  | .yield values => values.eval env

def Return.eval (term : Return Result Γ) (env : Env Γ) : Env Result :=
  match term with
  | .ret values => values.eval env

/-- A source tick executes the before region and either the after region
(on true) or the parent continuation (on false). -/
def While.runFrom (loop : While Op Input Result) (evalOp : Eval Op) (input : Env Input) :
    Nat → Env loop.State → Option (Env Result)
  | 0, _ => none
  | fuel + 1, state =>
      let (test, payload) := loop.before.eval evalOp Condition.eval (state.append input)
      if test then
        let next := loop.after.eval evalOp Yield.eval (payload.append input)
        loop.runFrom evalOp input fuel next
      else
        some (loop.cont.eval evalOp Return.eval (payload.append input))

def While.run (loop : While Op Input Result) (evalOp : Eval Op)
    (fuel : Nat) (input : Env Input) : Option (Env Result) :=
  loop.runFrom evalOp input fuel (loop.init.eval input)

/-- Divergence means execution fails to return at every finite budget. -/
def While.Diverges (loop : While Op Input Result) (evalOp : Eval Op) (input : Env Input) : Prop :=
  ∀ fuel, loop.run evalOp fuel input = none

/-- The distinct successor blocks introduced by flattening a while.
The entry is stored separately in `CF.Cfg`. -/
inductive Label (State Payload : List Width) : List Width → Type where
  | before : Label State Payload State
  | after : Label State Payload Payload
  | exit : Label State Payload Payload

def Condition.lower (term : Condition Payload Γ) : CF.Terminator (Label State Payload) Result Γ :=
  match term with
  | .condition test values => .condBr test ⟨.after, values⟩ ⟨.exit, values⟩

def Yield.lower (term : Yield State Γ) : CF.Terminator (Label State Payload) Result Γ :=
  match term with
  | .yield values => .br ⟨.before, values⟩

def Return.lower (term : Return Result Γ) : CF.Terminator (Label State Payload) Result Γ :=
  match term with
  | .ret values => .ret values

/-- Branch from the entry to before. A true condition goes to after, which
branches back to before. A false condition goes to exit, which runs the
parent continuation with the while results as block arguments. -/
def While.lower (loop : While Op Input Result) :
    CF.Cfg Op (Label loop.State loop.Payload) Input Result where
  entry := .terminator (.br ⟨.before, loop.init⟩)
  block
    | .before => loop.before.mapTerm Condition.lower
    | .after => loop.after.mapTerm Yield.lower
    | .exit => loop.cont.mapTerm Return.lower

end Silmaril.MLIR.SCF
