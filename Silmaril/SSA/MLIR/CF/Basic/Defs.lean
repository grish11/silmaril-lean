module

public import Silmaril.SSA.MLIR.Pure.Defs

/-! Typed block arguments, branches and execution for a pure CF fragment. -/

@[expose] public section

namespace Silmaril.MLIR.CF

open Arith (Width Var Env)
open Silmaril.MLIR.Pure (Code Eval Operands OpSignature i1)

/-- An edge pairs a successor label with operands matching its argument types
in order. The label family may contain several labels with the same types. -/
structure Edge (Label : List Width → Type) (Γ : List Width) where
  {argsTy : List Width}
  label : Label argsTy
  args : Operands Γ argsTy

/-- CF branches and a return to the enclosing fragment boundary. -/
inductive Terminator (Label : List Width → Type) (Result Γ : List Width) where
  | br (dest : Edge Label Γ)
  | condBr (test : Var Γ i1) (ifTrue ifFalse : Edge Label Γ)
  | ret (values : Operands Γ Result)

abbrev Block (Op : OpSignature) (Label : List Width → Type) (Γ Result : List Width) :=
  Code Op (Terminator Label Result) Γ

/-- The entry has the external input and is outside the label family, so no
edge targets it. Successor blocks see their own arguments and the dominating
entry arguments. Other inter-block values must be passed on edges. -/
structure Cfg (Op : OpSignature) (Label : List Width → Type) (Input Result : List Width) where
  entry : Block Op Label Input Result
  block : ∀ {args}, Label args → Block Op Label (args ++ Input) Result

/-- A successor together with its evaluated block arguments. -/
structure Frame (Label : List Width → Type) where
  {argsTy : List Width}
  label : Label argsTy
  args : Env argsTy

variable {Op : OpSignature} {Label : List Width → Type} {Input Result Γ : List Width}

def Edge.eval (edge : Edge Label Γ) (env : Env Γ) : Frame Label :=
  ⟨edge.label, edge.args.eval env⟩

def Terminator.eval (env : Env Γ) : Terminator Label Result Γ → Frame Label ⊕ Env Result
  | .br dest => .inl (dest.eval env)
  | .condBr test ifTrue ifFalse =>
      .inl (if (env.get test).getLsbD 0 then ifTrue.eval env else ifFalse.eval env)
  | .ret values => .inr (values.eval env)

/-- One unit of fuel executes a whole block, including its terminator.
Exhausting a finite budget yields `none`. Every executed block either takes
a typed edge or returns the fragment's result. -/
def Cfg.runBlock (cfg : Cfg Op Label Input Result) (evalOp : Eval Op) (input : Env Input) :
    Nat → {Δ : List Width} → Block Op Label Δ Result → Env Δ → Option (Env Result)
  | 0, _, _, _ => none
  | fuel + 1, _, block, env =>
      match block.eval evalOp (fun term vals => term.eval vals) env with
      | .inl next =>
          cfg.runBlock evalOp input fuel (cfg.block next.label) (next.args.append input)
      | .inr result => some result

def Cfg.runFrom (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (fuel : Nat) (input : Env Input) (frame : Frame Label) : Option (Env Result) :=
  cfg.runBlock evalOp input fuel (cfg.block frame.label) (frame.args.append input)

def Cfg.run (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (fuel : Nat) (input : Env Input) : Option (Env Result) :=
  cfg.runBlock evalOp input fuel cfg.entry input

/-- Divergence means execution fails to return at every finite budget. -/
def Cfg.Diverges (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) : Prop :=
  ∀ fuel, cfg.run evalOp fuel input = none

end Silmaril.MLIR.CF
