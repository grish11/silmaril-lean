module

public import Silmaril.Wasm.Abstract.CallXT.Defs
import Silmaril.Proofs.Wasm.Abstract.CallXT.Basic

/-!
# The extended relation with typed callee arities: theorems

* `EvalOXT.forget`: every `EvalOXT C` run is an `EvalOX C` run with the same
  outcome. The arity premises only strengthen the derivation.
* `evalOXT_iff_evalOX`: on code without `call_indirect`/`call_ref`
  (`irFreeL`), the two are the same.

**Not yet.** The discharge from typing: on typed stores and validated code,
every `EvalOX` run is an `EvalOXT` run (for `call_indirect` from the successful
`ref.cast`, for `call_ref` from the reference's type).
-/

public section

namespace Silmaril.Wasm.Abstract.CallXT

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX

variable {H : Type}

/-- **Forgetting the arity premises.** -/
theorem EvalOXT.forget {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOXT C s f stk es r) :
    EvalOX C s f stk es r :=
  Silmaril.Proofs.Wasm.Abstract.CallXT.forget h

/-- **Conservativity.** Without indirect and reference calls, the arity premises
are vacuous. -/
theorem evalOXT_iff_evalOX {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (hx : irFreeL es = true) :
    EvalOXT C s f stk es r ↔ EvalOX C s f stk es r :=
  ⟨EvalOXT.forget, fun h => Silmaril.Proofs.Wasm.Abstract.CallXT.of_irFree h hx⟩

end Silmaril.Wasm.Abstract.CallXT
