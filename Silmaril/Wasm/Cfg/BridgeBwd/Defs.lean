module

public import Silmaril.Wasm.Binaryen.Syntax

@[expose] public section

/-!
# The backward bridge: the fragment without tail calls

`tailFree e`: no `return_call`, `return_call_indirect` or `return_call_ref` in the tree. Direct,
indirect and reference calls are allowed. A tail call ends a region run in a *pending* tail call
(`Region.Out.tail`), answered only at the frame; the backward bridge states that case
separately.
-/

namespace Silmaril.Wasm.Cfg.Bridge

open Silmaril.Wasm Silmaril.Wasm.Binaryen

/-- The tail call forms. -/
def isTailCall : Instr → Bool
  | .returnCall _ | .returnCallIndirect _ _ | .returnCallRef _ => true
  | _ => false

mutual

/-- No tail call in the tree. -/
def tailFree : BExpr → Bool
  | .op i args => !isTailCall i && tailFreeL args
  | .block _ body => tailFreeL body
  | .loop _ body => tailFreeL body
  | .if_ _ c t e => tailFreeL c && tailFreeL t && tailFreeL e
  | .tryTable _ _ body => tailFreeL body

/-- `tailFree` on every tree of a list. -/
def tailFreeL : List BExpr → Bool
  | [] => true
  | e :: es => tailFree e && tailFreeL es

end

end Silmaril.Wasm.Cfg.Bridge
