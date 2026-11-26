module

public import Silmaril.SSA.LambdaRTL.CFG.Defs

/-!
# Lexical execution of a forward CFG

Every named block starts with the graph's input environment and its own
parameter. Local assignments in a block, including case payload bindings,
affect its own jump argument. A successor receives that argument, while other
values live across a block boundary must come from the graph input or be
passed explicitly in the argument. The suffix scan gives the same label
lookup convention as mutable CFG execution.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [Monad M] [DecidableEq V]

/-- Execute one block body and obtain its outgoing label and payload. -/
def Body.evalJump (body : Body V K F) (model : Model F M α) (env : V → α) : M (K × α) :=
  body.exec model (fun target payload _ => pure (target, payload)) env

variable [DecidableEq K]

/-- Advance the pending transfer past one labelled block. On a hit, enter
with the initial environment extended by the incoming argument. -/
def stepSSA (model : Model F M α) (input : V → α) (transfer : K × α)
    (block : K × Block V K F) : M (K × α) :=
  if transfer.1 = block.1 then
    block.2.body.evalJump model (upd input block.2.param transfer.2)
  else
    pure transfer

/-- Direct lexical execution on the flat block list. The pending transfer
after the last candidate block is the graph's exit and payload. -/
def _root_.Silmaril.SSA.LambdaRTL.CFG.runSSA (graph : CFG V K F)
    (model : Model F M α) (input : V → α) : M (K × α) := do
  let transfer ← graph.entry.evalJump model input
  graph.blocks.foldlM (stepSSA model input) transfer

end Silmaril.SSA.LambdaRTL.CFG
