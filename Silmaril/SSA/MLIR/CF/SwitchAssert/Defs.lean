module

public import Silmaril.SSA.MLIR.CF.Basic

/-! `cf.switch` and `cf.assert` over the Basic fragment's typed edges and scopes. -/

@[expose] public section

namespace Silmaril.MLIR.CF.SwitchAssert

open Arith (Width Var Env)
open Silmaril.MLIR.Pure (Eval Operands OpSignature i1)

/-- MLIR's `IntegerType::kMaxWidth` at llvm-project fb29ca8163c3309160711e5a14eb46bc6d4fdad2.
`Width` already requires a positive width. -/
def maxSwitchWidth : Nat := 2 ^ 24 - 1

/-- Case constants are bit patterns of the flag's signless integer type. Each
unique pattern is paired with one typed edge, and the default is a typed edge. -/
structure Switch (Label : List Width → Type) (Γ : List Width) where
  {width : Width}
  flag : Var Γ width
  widthSupported : width.val ≤ maxSwitchWidth
  defaultEdge : Edge Label Γ
  cases : List (BitVec width.val × Edge Label Γ)
  unique : (cases.map Prod.fst).Nodup

variable {Op : OpSignature} {Label : List Width → Type} {Input Result Γ : List Width}

/-- Choose a successor by full-width equality, falling back to the default. -/
def Switch.select (branch : Switch Label Γ) (env : Env Γ) : Edge Label Γ :=
  let flag := env.get branch.flag
  match branch.cases.find? (fun entry => entry.1 == flag) with
  | some (_, edge) => edge
  | none => branch.defaultEdge

inductive Terminator (Label : List Width → Type) (Result Γ : List Width) where
  | basic (term : CF.Terminator Label Result Γ)
  | switch (branch : Switch Label Γ)

def Terminator.eval (env : Env Γ) : Terminator Label Result Γ → Frame Label ⊕ Env Result
  | .basic term => term.eval env
  | .switch branch => .inl ((branch.select env).eval env)

/-- An assertion is a nonterminator that binds no value. Its continuation stays
in the same scope, and its message is a static attribute. -/
inductive Block (Op : OpSignature) (Label : List Width → Type) (Result : List Width) :
    List Width → Type where
  | terminator {Γ : List Width} (term : Terminator Label Result Γ) : Block Op Label Result Γ
  | letOp {Γ args : List Width} {w : Width} (op : Op args w) (operands : Operands Γ args)
      (rest : Block Op Label Result (w :: Γ)) : Block Op Label Result Γ
  | assert {Γ : List Width} (test : Var Γ i1) (message : String)
      (rest : Block Op Label Result Γ) : Block Op Label Result Γ

/-- `none` means assertion failure. A successful block takes an edge or returns.
A true assertion continues in place. A false assertion skips the rest of the
block. The pure observation abstracts away diagnostic output. -/
def Block.eval (evalOp : Eval Op) :
    {Γ : List Width} → Block Op Label Result Γ → Env Γ → Option (Frame Label ⊕ Env Result)
  | _, .terminator term, env => some (term.eval env)
  | _, .letOp op args rest, env => rest.eval evalOp (.cons (evalOp op (args.eval env)) env)
  | _, .assert test _ rest, env =>
      if (env.get test).getLsbD 0 then rest.eval evalOp env else none

/-- Uses the Basic fragment's entry and block argument discipline. Each
successor receives its own arguments followed by the dominating entry input. -/
structure Cfg (Op : OpSignature) (Label : List Width → Type) (Input Result : List Width) where
  entry : Block Op Label Result Input
  block : ∀ {args}, Label args → Block Op Label Result (args ++ Input)

/-- A terminal fragment outcome. An exhausted run has no outcome at its budget. -/
inductive Outcome (Result : List Width) where
  | returned (values : Env Result)
  | aborted

/-- One unit of fuel executes a block, including all its assertions. -/
def Cfg.runBlock (cfg : Cfg Op Label Input Result) (evalOp : Eval Op) (input : Env Input) :
    Nat → {Δ : List Width} → Block Op Label Result Δ → Env Δ → Option (Outcome Result)
  | 0, _, _, _ => none
  | fuel + 1, _, block, env =>
      match block.eval evalOp env with
      | some (.inl next) =>
          cfg.runBlock evalOp input fuel (cfg.block next.label) (next.args.append input)
      | some (.inr result) => some (.returned result)
      | none => some .aborted

def Cfg.run (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (fuel : Nat) (input : Env Input) : Option (Outcome Result) :=
  cfg.runBlock evalOp input fuel cfg.entry input

/-- A divergent execution has neither returned nor aborted at any finite budget. -/
def Cfg.Diverges (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) : Prop :=
  ∀ fuel, cfg.run evalOp fuel input = none

def Block.embed : {Γ : List Width} → CF.Block Op Label Γ Result → Block Op Label Result Γ
  | _, .terminator term => .terminator (.basic term)
  | _, .letOp op operands rest => .letOp op operands (Block.embed rest)

/-- Include a Basic CFG, retaining its input, labels, block arguments and result. -/
def Cfg.embed (cfg : CF.Cfg Op Label Input Result) : Cfg Op Label Input Result where
  entry := Block.embed cfg.entry
  block label := Block.embed (cfg.block label)

end Silmaril.MLIR.CF.SwitchAssert
