module

public import Silmaril.Wasm.Cfg.Region.Defs
public import Silmaril.Wasm.Abstract.CallX.Defs

@[expose] public section

/-!
# The bridge from extended native trees to the region semantics: definitions

`CallX.EvalOX C` runs folded trees (`Binaryen.BExpr`) on a top-first stack; `Region.RunC P host C`
runs their lowering (`expression (lowerList es)`) on a bottom-first stack. Both answer every
resolved call by the same oracle `C`. They differ in what a run *ends* with:

* a region run stops at a tail call with a **pending** tail call (`Out.tail W a c`), answered
  only when the frame is left; `EvalOX` answers it at once (`EvalOX.tail`), ending with the
  callee's store and the caller's flow `CallX.tailFlow rs.length fl`;
* branches and returns carry, in the region semantics, the values of the enclosing labels too
  (`labelBrSucc`, `labelRet`), the native flow only the innermost ones;
* an unresolved tail call of null traps natively at once, and in the region semantics when the
  frame is left (`Out.tailNull`).

`ResOut C s' f' o r` relates a region end (store `s'`, frame `f'`, outcome `o`) to a native
result `r`: for a pending tail call, the oracle's answer to it (on the top `ps.length` values, as
`Machine.EndsC` answers it) gives `r`; otherwise the store and frame agree and `FlowRel` relates
the flows (`Interp.FlowMatch`, plus exceptions and null tails).
-/

namespace Silmaril.Wasm.Cfg.Bridge

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Cfg.Region

variable {H : Type}

/-- **A native flow and a region outcome that end alike** (store and frame aside). Values are
top-first natively and bottom-first in the region; a branch or return in the region may carry
values of enclosing labels under the native ones. -/
def FlowRel : Flow → Region.Out → Prop
  | .normal vs, .normal ws => ws = vs.reverse
  | .brk l vs, .br l' ws => l' = l ∧ ∃ junk, ws = junk ++ vs.reverse
  | .ret vs, .ret ws => ∃ junk, ws = junk ++ vs.reverse
  | .trap, .trap => True
  | .trap, .tailNull _ _ => True
  | .throw t, .throw t' => t' = t
  | _, _ => False

/-- **A region end resolved as a native result.** A pending tail call of `a` over `W` is
answered by `C` on the top `ps.length` values of `W` (from the region's final store), and the
native result is the callee's store, the caller's frame and `tailFlow rs.length` of the callee's
flow. Any other outcome: same store and frame, and `FlowRel`. -/
def ResOut (C : Abstract.CallRel H) (s' : Store H) (f' : Frame) : Region.Out → Store H × Frame × Flow → Prop
  | .tail W a _, r => ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (W₀ args : List Val)
      (fl : Flow), s'.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      W = W₀ ++ args ∧ args.length = ps.length ∧ C s' a args (r.1, fl) ∧
      ((∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) ∧ r.2.1 = f' ∧
      r.2.2 = Abstract.CallX.tailFlow rs.length fl
  | o, r => r.1 = s' ∧ r.2.1 = f' ∧ FlowRel r.2.2 o

end Silmaril.Wasm.Cfg.Bridge
