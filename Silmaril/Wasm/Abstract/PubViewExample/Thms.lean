module

public import Silmaril.Wasm.Abstract.PubViewExample.Defs
public import Silmaril.Wasm.Abstract.PubView.Thms
import Silmaril.Proofs.Wasm.Abstract.PubViewExample.Basic

/-!
# A store view that identifies an internal call with its inlining: theorems

The export `"f"` of `callMod` calls an internal helper that returns `42`. The export of
`inlineMod` returns `42` directly. Internal calls are Core steps, not host events, so the
public interaction does not show the call. It does show the final store, and the two stores
differ in the code of function `0`:

* **the runs** (`callStore_run`, `inlineStore_run`): each invocation on no arguments returns
  `[i32 42]` in its own unchanged store, with the empty host log. These are explicit Core runs,
  checked step by step by inversion: the run through the helper takes seven steps and the
  inlined run takes three. Every other configuration reachable from the invocation lies on that
  run, and none of them diverges;
* **admission** (`invOk_callStore_iff`, `invOk_inlineStore_iff`): `InvOk` (a typed store that
  passes the arity check, and a typed invocation) admits exactly the empty argument list. The
  typing comes from the instantiation of the validated modules;
* **through the view** (`pubEquivV_inline`): the two exports are `PubEquivV codeView`;
* **exactly** (`pubEquiv_inline_not`): they are not `PubEquiv`, because the final store of the
  first return is not a final store of the second export;
* **strategies** (`viewStrat_inline`, `pubStrat_inline_ne`): the view strategies are equal and
  the public strategies of `PubModule` are not. `codeView` factors every host
  (`hostView_codeView`), so `viewStrat_eq_iff` applies.

So the view `codeView` alone makes the two exports equal: it identifies an export that makes an
internal call with the export where that call is inlined.

**Scope.**
* **One host.** The host function type is `Empty`, so the only host is the empty relation
  (`host_eq`) and there are no host calls. The statements quantify over `host`, but that adds
  nothing.
* **Every profile.** Each statement holds at each profile `P` separately, including the
  deterministic `SingleThreaded.profile o`. The runs use no numeric operation.
* **Native stores, no exceptions**, as in `PubModule` and `PubView`.
* **Not contextual full abstraction.** This is one pair of exports, observed against one host
  through one view. It says nothing about other hosts or other contexts.
* **Why the view forgets code.** The stores differ only in code, so a view that keeps code
  keeps them apart.

Proofs are in `Silmaril.Proofs.Wasm.Abstract.PubViewExample.Basic`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.PubViewExample

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Numerics (Profile)

/-! ## The stores -/

/-- With host function type `Empty`, every host is the empty relation. -/
theorem host_eq (host : HostSemantics Empty) : host = fun _ _ _ _ => False :=
  Silmaril.Proofs.Wasm.Abstract.PubViewExample.host_eq host

/-- The two stores differ (in the body of function `0`). -/
theorem callStore_ne_inlineStore : callStore ≠ inlineStore :=
  Silmaril.Proofs.Wasm.Abstract.PubViewExample.callStore_ne_inlineStore

/-- The two stores have the same view. -/
theorem codeView_eq : codeView callStore = codeView inlineStore :=
  Silmaril.Proofs.Wasm.Abstract.PubViewExample.codeView_eq

/-- `InvOk` admits the export of `callMod` exactly on the empty argument list. -/
theorem invOk_callStore_iff (vs : List Val) : InvOk callStore (0, vs) ↔ vs = [] :=
  Silmaril.Proofs.Wasm.Abstract.PubViewExample.invOk_callStore_iff vs

/-- `InvOk` admits the export of `inlineMod` exactly on the empty argument list. -/
theorem invOk_inlineStore_iff (vs : List Val) : InvOk inlineStore (0, vs) ↔ vs = [] :=
  Silmaril.Proofs.Wasm.Abstract.PubViewExample.invOk_inlineStore_iff vs

/-! ## The runs -/

/-- **The export with the internal call returns `42`**, with no host event and its store
unchanged. -/
theorem callStore_run (P : Profile) (host : HostSemantics Empty) :
    EvRun P host (invoke callStore 0 []) [] ⟨callStore, {}, vals [.i32 42]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.PubViewExample.evRun_iff.mpr
    ⟨rfl, Silmaril.Proofs.Wasm.Abstract.PubViewExample.callRun.steps⟩

/-- **The inlined export returns `42`**, with no host event and its store unchanged. -/
theorem inlineStore_run (P : Profile) (host : HostSemantics Empty) :
    EvRun P host (invoke inlineStore 0 []) [] ⟨inlineStore, {}, vals [.i32 42]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.PubViewExample.evRun_iff.mpr
    ⟨rfl, Silmaril.Proofs.Wasm.Abstract.PubViewExample.inlineRun.steps⟩

/-! ## Equivalence -/

/-- **Through `codeView`, the export with the internal call and the inlined export are
publicly equivalent**, at every profile, on the invocations admitted by `InvOk`. -/
theorem pubEquivV_inline (P : Profile) (host : HostSemantics Empty) :
    PubEquivV codeView P host InvOk callStore 0 inlineStore 0 :=
  Silmaril.Proofs.Wasm.Abstract.PubViewExample.pubEquivV_of_spec
    Silmaril.Proofs.Wasm.Abstract.PubViewExample.callSpec
    Silmaril.Proofs.Wasm.Abstract.PubViewExample.inlineSpec codeView_eq

/-- **Without the view they are not equivalent**: `PubEquiv` compares final stores exactly. -/
theorem pubEquiv_inline_not (P : Profile) (host : HostSemantics Empty) :
    ¬ PubEquiv P host InvOk callStore 0 inlineStore 0 :=
  Silmaril.Proofs.Wasm.Abstract.PubViewExample.not_pubEquiv_of_spec
    Silmaril.Proofs.Wasm.Abstract.PubViewExample.callSpec
    Silmaril.Proofs.Wasm.Abstract.PubViewExample.inlineSpec callStore_ne_inlineStore

/-- Every host factors through `codeView`: there are no host functions. -/
theorem hostView_codeView (host : HostSemantics Empty) : HostView codeView host :=
  fun hh => hh.elim

/-- **The view strategies of the two exports are equal.** -/
theorem viewStrat_inline (P : Profile) (host : HostSemantics Empty) :
    viewStrat codeView P host InvOk callStore 0 = viewStrat codeView P host InvOk inlineStore 0 :=
  (viewStrat_eq_iff (hostView_codeView host)).mpr (pubEquivV_inline P host)

/-- **The public strategies of the two exports differ.** -/
theorem pubStrat_inline_ne (P : Profile) (host : HostSemantics Empty) :
    pubStrat P host InvOk callStore 0 ≠ pubStrat P host InvOk inlineStore 0 :=
  fun h => pubEquiv_inline_not P host (pubStrat_eq_iff.mp h)

end Silmaril.Wasm.Abstract.PubViewExample
