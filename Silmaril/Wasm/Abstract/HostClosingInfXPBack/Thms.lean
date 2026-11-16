module

public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Wasm.Interp.PProgress.Thms
import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.Closed

/-!
# Core to the canonical closure, divergent runs: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack`. The backward direction (Core to
canonical) for divergent runs, starting with host-free divergence. Deterministic profile
`SingleThreaded.profile o`; the store may hold host functions.

**Host-free Core divergence is closed canonical divergence** (the base case of divergence after a
log, `LogDivXP.div`, and of `FunDivXP` descents):

* `evalDivXP_of_diverges`: a typed problem (`Interp.TypedP tags`: checked by `ehExt tags` in a
  checked store with the tag invariants, typed in some context, valid instance types) whose Core
  run diverges host-free diverges in the closed canonical semantics (`XDivergeP.EvalDivXP`);
* `funDivXP_of_invoke_diverges`: a typed invocation (`StoreOk s`, `InvokeOk s a vs`,
  `Interp.StoreChkE (Interp.ehExt tags) s.funcs`, `Interp.TagsOk tags s`) diverging host-free in
  Core is `XDivergeP.FunDivXP s a vs`;
* `invoke_diverges_iff_funDivXP_of`: with `Interp.PProgress.invoke_diverges_of_funDivXP`, both ways.
  `Interp.PProgress.invoke_diverges_iff_funDivXP` also assumes a store of Wasm functions only
  (`Interp.WasmFuncsT`); this drops that assumption.

Proof (`Reach`, `Run`, `Progress`, `Closed`): `Interp.evalDivXP_of_noOutcome`'s joint coinduction
with `WasmFuncsT` replaced by the absence of a **closed reach of a host call** (`HReach`,
`HCallReach`: the unfoldings of `DivStepXP`/`CallStepXP`, ending at a call to a host function); the
callee function types then come from typing (`HostClosingXP.funcType_of_indRes`,
`funcType_of_callRef_cfg`, `funcType_of_returnCallRef_site`). A closed reach is a Core run, in any
active context, to a configuration at a host call (the steps of `Interp.progressP`), and a closed
outcome is a Core run to a final form (`Interp.evalOXP_closed_good`); neither has a host-free step,
so neither exists for a problem whose Core run diverges host-free (`diverges_through_steps`).

Not yet: divergence after a nonempty log and productive runs, Core to `wasmEvFunDXP` and
`wasmEvInfNXP`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (TypedP StoreChkE ehExt TagsOk)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type} {o : GrowOracle} {tags : List TagInst}

/-- **Host-free Core divergence of a typed problem is closed canonical divergence**
(deterministic profile). -/
theorem evalDivXP_of_diverges {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} (ht : TypedP tags s f stk es)
    (hd : Diverges (profile o) (fun _ _ _ _ => False)
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩) :
    EvalDivXP s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.evalDivXP_of_diverges ht hd

/-- **Host-free Core divergence of a typed invocation is `FunDivXP`** (deterministic profile),
on a store that may hold host functions. -/
theorem funDivXP_of_invoke_diverges {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hd : Diverges (profile o) (fun _ _ _ _ => False) (invoke s a vs)) : FunDivXP s a vs :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.funDivXP_of_invoke_diverges hs hok hS hts hd

/-- **Host-free Core divergence of a typed invocation is exactly `FunDivXP`** (deterministic
profile), on a store that may hold host functions. -/
theorem invoke_diverges_iff_funDivXP_of {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) :
    Diverges (profile o) (fun _ _ _ _ => False) (invoke s a vs) ↔ FunDivXP s a vs :=
  ⟨funDivXP_of_invoke_diverges hs hok hS hts,
    Silmaril.Wasm.Interp.PProgress.invoke_diverges_of_funDivXP hS hts hok⟩

end Silmaril.Wasm.Abstract
