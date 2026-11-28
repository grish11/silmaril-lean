module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Defs

/-! # The leading saved definitions of a typed preheader -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input Γ : List Width} {saved carried result w : Width} {extra : List Width}

/-- Typed leading lets, independent of the outgoing label family. The last
let extends the most recent slot of the preheader environment. -/
inductive Prefix (Input : List Width) : List Width → Type where
  | nil : Prefix Input Input
  | snoc {Γ args : List Width} {w : Width} (prior : Prefix Input Γ)
      (op : TargetOp args w) (operands : Operands Γ args) : Prefix Input (w :: Γ)

def Prefix.wrap : {Γ : List Width} → Prefix Input Γ →
    Block TargetOp (Label saved carried result extra) Γ [result] →
    Block TargetOp (Label saved carried result extra) Input [result]
  | _, .nil, tail => tail
  | _, .snoc prior op operands, tail => prior.wrap (.letOp op operands tail)

def Prefix.eval (input : Env Input) : {Γ : List Width} → Prefix Input Γ → Env Γ
  | _, .nil => input
  | _, .snoc prior op operands =>
    let env := prior.eval input
    .cons (evalOp op (operands.eval env)) env

/-- Split at the cut after the supplied saved definitions. Check the width
of each actual let in evaluation order (the requested widths are newest first). -/
def splitPrefix? (code : Block TargetOp (Label saved carried result extra) Input [result]) :
    (widths : List Width) → Option
      (Prefix Input (widths ++ Input) × Block TargetOp (Label saved carried result extra) (widths ++ Input) [result])
  | [] => some (.nil, code)
  | width :: prior => do
    let (leading, rest) ← splitPrefix? code prior
    match rest with
    | .terminator _ => none
    | .letOp (w := actual) op operands tail =>
      if same : actual = width then
        some (same ▸ (Prefix.snoc leading op operands, tail))
      else none

/-- The actual preheader prefix computes the values assumed by routing. -/
def Prefix.Matches (code : Block TargetOp (Label saved carried result extra) Input [result])
    (input : Env Input) {widths : List Width} (values : Env widths) : Prop :=
  ∃ leading tail, splitPrefix? code widths = some (leading, tail) ∧
    leading.eval input = values.append input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved
