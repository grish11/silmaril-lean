module

public import Silmaril.Wasm.Abstract.XRecursion.Defs
public import Silmaril.Wasm.Abstract.Recursion.Defs
public import Silmaril.Wasm.Abstract.CallX.Thms
import Silmaril.Proofs.Wasm.Abstract.XRecursion.Basic

/-!
# Closing the extended call forms: theorems

* `closedCallX_fixpoint`: the closure answers each call, of any call form, by
  running the callee's body with the closure.
* `closedCallX_funcs`: closed calls keep the store's functions.
* **The direct part is the native closure.** `closedCall_le_closedCallX`: every
  answer of `closedCall` is one of `closedCallX`. On stores whose functions
  have no extended call form (`StoreXFree`), they agree (`closedCallX_iff`),
  direct code runs alike (`evalOX_closed_iff`), and so do invocations
  (`closedOutcomeX_iff`).
* **Exposure, closed.** `evalOX_closed_exposed`: outcomes of the closed extended
  semantics (other than traps) are exactly the finished paths of the exposed
  body `CallX.denListX` whose call events `closedCallX` answers.

**Not here.** Divergence (no outcome is not divergence on untyped code), and
Core 3.0 adequacy of the extended rules.
-/

public section

namespace Silmaril.Wasm.Abstract.XRecursion

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel EvalO closedCall ClosedOutcome)
open Silmaril.Wasm.Abstract.CallX

variable {H : Type}

theorem closedCallX_fixpoint : (closedCallX : CallRel H) = bodyCallX closedCallX :=
  Silmaril.Proofs.Wasm.Abstract.XRecursion.closedCallX_eq_bodyCallX

theorem closedCallX_funcs {s : Store H} {a : Nat} {args : List Val} {out : Store H × Flow}
    (h : closedCallX s a args out) : out.1.funcs = s.funcs :=
  Silmaril.Proofs.Wasm.Abstract.XRecursion.closedCallX_funcs s a args out h

/-- Flat instructions keep the store's functions. -/
theorem evalFlat_funcs {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr} {fl : Flow}
    (h : evalFlat s f stk i = some (s', f', fl)) : s'.funcs = s.funcs :=
  Silmaril.Proofs.Wasm.Abstract.XRecursion.evalFlat_funcs h

/-- Runs keep the store's functions when their oracle does. -/
theorem evalOX_funcs {C : CallRel H} (hC : ∀ s a args out, C s a args out → out.1.funcs = s.funcs)
    {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow}
    (h : EvalOX C s f stk es r) : r.1.funcs = s.funcs :=
  Silmaril.Proofs.Wasm.Abstract.XRecursion.evalOX_funcs hC h

theorem closedCall_le_closedCallX : (closedCall : CallRel H) ≤ closedCallX :=
  Silmaril.Proofs.Wasm.Abstract.XRecursion.closedCall_le_closedCallX

/-- **On direct stores the extended closure is `closedCall`.** -/
theorem closedCallX_iff {s : Store H} (hs : StoreXFree s) {a : Nat} {args : List Val}
    {out : Store H × Flow} : closedCallX s a args out ↔ closedCall s a args out :=
  Silmaril.Proofs.Wasm.Abstract.XRecursion.closedCallX_iff hs

theorem evalOX_closed_iff {s : Store H} (hs : StoreXFree s) {f : Frame} {stk : List Val}
    {es : List BExpr} (hx : xFreeL es = true) {r : Store H × Frame × Flow} :
    EvalOX closedCallX s f stk es r ↔ EvalO closedCall s f stk es r :=
  Silmaril.Proofs.Wasm.Abstract.XRecursion.evalOX_closed_iff hs hx

theorem closedOutcomeX_iff {s : Store H} (hs : StoreXFree s) {a : Nat} {vs : List Val}
    {s' : Store H} {fl : Flow} : ClosedOutcomeX s a vs s' fl ↔ ClosedOutcome s a vs s' fl :=
  Silmaril.Proofs.Wasm.Abstract.XRecursion.closedOutcomeX_iff hs

open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.BodyTrace (Path)

/-- **Exposure, closed.** -/
theorem evalOX_closed_exposed {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {s' : Store H} {f' : Frame} {fl : Flow} (hfl : fl ≠ .trap) :
    EvalOX closedCallX s f stk es (s', f', fl) ↔
      ∃ cs, Answered closedCallX cs ∧
        Path (((denListX es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs
          (.val (.ok (⟨(f', fl)⟩, ⟨s'⟩))) :=
  evalOX_iff hfl

end Silmaril.Wasm.Abstract.XRecursion
