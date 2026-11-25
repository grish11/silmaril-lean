module

public import Silmaril.SSA.MLIR.SCF.While.Defs

/-! A result-bearing if with an optional while in each arm, lowered to one CF graph. -/

@[expose] public section

namespace Silmaril.MLIR.SCF.IfWhile

open Arith (Width Var Env)
open Silmaril.MLIR.Pure (Code Eval Operands OpSignature i1)

variable {Op : OpSignature} {Input Joined Result : List Width}

/-- At the while site, select the initial loop state and the arm-local values
that remain in scope throughout the while and its arm continuation. -/
structure Enter (State Captures Γ : List Width) where
  init : Operands Γ State
  captures : Operands Γ Captures

def Enter.eval {State Captures Γ : List Width} (term : Enter State Captures Γ) (env : Env Γ) :
    Env State × Env Captures :=
  (term.init.eval env, term.captures.eval env)

/-- The prefix ends at the while site. The before and after regions see their
arguments, arm-local captures, and parent inputs in that order. The arm tail
sees the while results in place of the region arguments and yields if results. -/
structure LoopArm (Op : OpSignature) (Input Joined : List Width) where
  State : List Width
  Payload : List Width
  Captures : List Width
  setup : Code Op (Enter State Captures) Input
  before : Code Op (Condition Payload) ((State ++ Captures) ++ Input)
  after : Code Op (Yield State) ((Payload ++ Captures) ++ Input)
  tail : Code Op (Yield Joined) ((Payload ++ Captures) ++ Input)

/-- An arm of `scf.if` takes no arguments and yields the if result tuple. -/
inductive Arm (Op : OpSignature) (Input Joined : List Width) where
  | straight (body : Code Op (Yield Joined) Input)
  | loop (body : LoopArm Op Input Joined)

/-- Both arms yield the same interface. The parent continuation has access
to those results and the original inputs. -/
structure Program (Op : OpSignature) (Input Result : List Width) where
  Joined : List Width
  test : Var Input i1
  onTrue : Arm Op Input Joined
  onFalse : Arm Op Input Joined
  cont : Code Op (Return Result) (Joined ++ Input)

/-- A before visit and its selected after region or arm tail take two ticks.
On success, return the yielded tuple and the unspent budget. -/
def LoopArm.runLoop (loop : LoopArm Op Input Joined) (evalOp : Eval Op)
    (input : Env Input) (captures : Env loop.Captures) :
    Nat → Env loop.State → Option (Env Joined × Nat)
  | 0, _ | 1, _ => none
  | fuel + 2, state =>
    let (test, payload) := loop.before.eval evalOp Condition.eval ((state.append captures).append input)
    let scope := (payload.append captures).append input
    if test then loop.runLoop evalOp input captures fuel (loop.after.eval evalOp Yield.eval scope)
    else some (loop.tail.eval evalOp Yield.eval scope, fuel)

/-- Spend one tick on the selected arm's body or while prefix. -/
def Arm.run (arm : Arm Op Input Joined) (evalOp : Eval Op) (input : Env Input) :
    Nat → Option (Env Joined × Nat)
  | 0 => none
  | fuel + 1 =>
    match arm with
    | .straight body => some (body.eval evalOp Yield.eval input, fuel)
    | .loop body =>
      let (state, captures) := body.setup.eval evalOp Enter.eval input
      body.runLoop evalOp input captures fuel state

/-- The shared parent continuation requires one tick. -/
def Program.runJoin (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) (values : Env program.Joined) : Nat → Option (Env Result)
  | 0 => none
  | _ + 1 => some (program.cont.eval evalOp Return.eval (values.append input))

/-- Spend one tick on the if test, execute the selected arm, and sequence its
yield to the shared parent continuation using the remaining budget. -/
def Program.run (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) : Nat → Option (Env Result)
  | 0 => none
  | fuel + 1 =>
    let arm := if (input.get program.test).getLsbD 0 then program.onTrue else program.onFalse
    (arm.run evalOp input fuel).bind (fun (values, rest) => program.runJoin evalOp input values rest)

def Program.Diverges (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) : Prop :=
  ∀ fuel, program.run evalOp input fuel = none

/-- Only looping arms allocate the three local successor blocks. -/
inductive Layout where
  | straight
  | loop (state payload captures : List Width)

abbrev Arm.layout : Arm Op Input Joined → Layout
  | .straight _ => .straight
  | .loop body => .loop body.State body.Payload body.Captures

inductive Layout.Label : Layout → List Width → Type where
  | entry {shape : Layout} : Label shape []
  | before {state payload captures : List Width} :
      Label (.loop state payload captures) (state ++ captures)
  | after {state payload captures : List Width} :
      Label (.loop state payload captures) (payload ++ captures)
  | exit {state payload captures : List Width} :
      Label (.loop state payload captures) (payload ++ captures)

/-- The two arms and the join have disjoint labels even when their argument
types coincide. -/
inductive Label (yes no : Layout) (joined : List Width) : List Width → Type where
  | onTrue {args : List Width} : yes.Label args → Label yes no joined args
  | onFalse {args : List Width} : no.Label args → Label yes no joined args
  | join : Label yes no joined joined

variable {Γ Δ Θ : List Width}

def weakenOperands {w : Width} : {Δ : List Width} → Operands Γ Δ → Operands (w :: Γ) Δ
  | _, .nil => .nil
  | _, .cons x xs => .cons (.there x) (weakenOperands xs)

def appendOperands : {Δ : List Width} → Operands Γ Δ → Operands Γ Θ → Operands Γ (Δ ++ Θ)
  | _, .nil, tail => tail
  | _, .cons x xs, tail => .cons x (appendOperands xs tail)

def frontOperands (args : List Width) : Operands (args ++ Γ) args :=
  match args with
  | [] => .nil
  | _ :: rest => .cons .here (weakenOperands (frontOperands rest))

/-- Refer to the capture slice immediately following the loop arguments. -/
def captureOperands (args captures : List Width) : Operands ((args ++ captures) ++ Γ) captures :=
  match args with
  | [] => frontOperands captures
  | _ :: rest => weakenOperands (captureOperands rest captures)

variable {Term Target : List Width → Type}

/-- Retain each operation and track the captured operand references through
its result binder before rewriting the terminator. -/
def mapWithCaptures (finish : ∀ {Ξ}, Term Ξ → Operands Ξ Δ → Target Ξ) :
    {Γ : List Width} → Code Op Term Γ → Operands Γ Δ → Code Op Target Γ
  | _, .terminator term, captures => .terminator (finish term captures)
  | _, .letOp op args rest, captures => .letOp op args (mapWithCaptures finish rest (weakenOperands captures))

variable {Dest : List Width → Type}

def lowerYield (dest : Dest Δ) : Yield Δ Γ → CF.Terminator Dest Result Γ
  | .yield args => .br ⟨dest, args⟩

def lowerEnter (dest : Dest (Δ ++ Θ)) (term : Enter Δ Θ Γ) : CF.Terminator Dest Result Γ :=
  .br ⟨dest, appendOperands term.init term.captures⟩

def lowerCondition (yes no : Dest (Δ ++ Θ)) :
    Condition Δ Γ → Operands Γ Θ → CF.Terminator Dest Result Γ
  | .condition test args, captures =>
    let values := appendOperands args captures
    .condBr test ⟨yes, values⟩ ⟨no, values⟩

def lowerBackedge (dest : Dest (Δ ++ Θ)) :
    Yield Δ Γ → Operands Γ Θ → CF.Terminator Dest Result Γ
  | .yield args, captures => .br ⟨dest, appendOperands args captures⟩

def lowerReturn : Return Result Γ → CF.Terminator Dest Result Γ
  | .ret values => .ret values

/-- Emit an arm block in its allocated label family. The only destination
outside that family is the shared join. -/
def Arm.lowerBlock : (arm : Arm Op Input Joined) →
    (inject : ∀ {args}, arm.layout.Label args → Dest args) → (join : Dest Joined) →
    {args : List Width} → arm.layout.Label args → CF.Block Op Dest (args ++ Input) Result
  | .straight body, _, join, _, .entry => body.mapTerm (lowerYield join)
  | .loop body, inject, _, _, .entry => body.setup.mapTerm (lowerEnter (inject .before))
  | .loop body, inject, _, _, .before =>
      mapWithCaptures (lowerCondition (inject .after) (inject .exit))
        body.before (captureOperands body.State body.Captures)
  | .loop body, inject, _, _, .after =>
      mapWithCaptures (lowerBackedge (inject .before))
        body.after (captureOperands body.Payload body.Captures)
  | .loop body, _, join, _, .exit => body.tail.mapTerm (lowerYield join)

/-- Flatten the if and both allocated arm subgraphs into one successor table. -/
def Program.lower (program : Program Op Input Result) :
    CF.Cfg Op (Label program.onTrue.layout program.onFalse.layout program.Joined) Input Result where
  entry := .terminator (.condBr program.test ⟨.onTrue .entry, .nil⟩ ⟨.onFalse .entry, .nil⟩)
  block
    | .onTrue label => program.onTrue.lowerBlock Label.onTrue .join label
    | .onFalse label => program.onFalse.lowerBlock Label.onFalse .join label
    | .join => program.cont.mapTerm lowerReturn

end Silmaril.MLIR.SCF.IfWhile
