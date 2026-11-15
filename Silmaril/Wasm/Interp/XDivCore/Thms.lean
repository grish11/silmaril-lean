module

public import Silmaril.Proofs.Wasm.Interp.XDivCore
public import Silmaril.Proofs.Wasm.Interp.XDivCoreT

/-!
# Extended divergence is Core 3.0 divergence (theorems)

The forward direction of divergence for the indirect and reference calls:

* `diverges_of_evalDivX`: a typed problem (`TypedX`, `irExt`-checked code) that diverges in the
  closed extended semantics (`XDiverge.EvalDivX`) diverges in Core 3.0, in any evaluation
  context, at every profile;
* `invoke_diverges_of_funDivX`: a typed invocation whose callee body diverges (`FunDivX`), in
  an `irExt`-checked typed store, diverges in Core 3.0.

With tail calls (checker `tExt`, `TypedT`), inside a frame (`InFrame`):

* `diverges_of_evalDivT`: every call form, a diverging tail callee included: its pending
  `return_call_ref` leaves the labels, replaces the frame, and the callee is entered;
* `invoke_diverges_of_funDivT`: the invocation form, for a `tExt`-checked typed store.

**Scope.** The converse (Core divergence is `EvalDivX`) is not stated here.
-/

public section

namespace Silmaril.Wasm.Interp.XDivCore

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.XDiverge

variable {H : Type} {P : Numerics.Profile}

/-- **Extended divergence is Core 3.0 divergence**, in any evaluation context. -/
theorem diverges_of_evalDivX {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} (hd : EvalDivX s f stk es) (ht : TypedX s f stk es)
    (E : Sim.ActiveCtx) :
    Diverges P noHostX
      (E.plug ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩) :=
  Silmaril.Wasm.Interp.diverges_of_evalDivX hd ht E

/-- **A diverging callee body makes its typed invocation diverge in Core 3.0.** -/
theorem invoke_diverges_of_funDivX {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE irExt s.funcs) (hd : FunDivX s a vs) :
    Diverges P noHostX (invoke s a vs) :=
  Silmaril.Wasm.Interp.invoke_diverges_of_funDivX hs hok hS hd

/-- **Extended divergence is Core 3.0 divergence, tail calls included**, inside a frame. -/
theorem diverges_of_evalDivT {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} (hd : EvalDivX s f stk es) (ht : TypedT s f stk es)
    {E : Sim.ActiveCtx} (hE : InFrame E) :
    Diverges P noHostX
      (E.plug ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩) :=
  Silmaril.Wasm.Interp.diverges_of_evalDivT hd ht hE

/-- **A diverging callee body makes its typed invocation diverge in Core 3.0**, every call
form included. -/
theorem invoke_diverges_of_funDivT {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hd : FunDivX s a vs) :
    Diverges P noHostX (invoke s a vs) :=
  Silmaril.Wasm.Interp.invoke_diverges_of_funDivT hs hok hS hd

end Silmaril.Wasm.Interp.XDivCore
