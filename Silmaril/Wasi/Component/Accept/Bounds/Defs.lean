module

public import Silmaril.Wasi.Component.Accept.Canon.Defs
public import Silmaril.Wasm.Component.Reference.Features.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Layout.Defs

/-! # Length bounds of component acceptors: the assumptions

A WASI component trace carries `list<u8>` values of any length: the world models of
`Silmaril.Wasi.World` impose no bound. Every bound on component acceptance therefore rests on
an **explicit canonical-ABI assumption**. Two are available.

* **Address width, through a core module** (`CanonLowerAcceptBy obs`): the component's lists
  are the segments the core module passes through `canon lower`, read by the decoder `obs`.
  `Callout.bytes32` is the 32-bit memory (`CanonLowerAccept` is this case); `Callout.bytes64`
  is `memory64`. The bound is then the module's: `< 2 ^ 32` or `< 2 ^ 64`.
* **The lift's length check** (`ListLiftChecked lim σ f`): every list crossing the boundary
  passed the canonical ABI's `load_list_from_range` check
  `length * elem_size ≤ MAX_LIST_BYTE_LENGTH` (it traps otherwise: `listTooLong` in
  `Silmaril.Wasm.Component.Canon.loadListFromRangeWith`), for the limits `lim`. For `u8` the
  element size is `1`, so the bound is `≤ lim.maxListBytes`: `2 ^ 28 - 1` for the
  specification's limits (`Limits.spec`) and `2 ^ 32 - 1` for wasmtime's (`Limits.wasmtime`).
  This is a hypothesis about the component's implementation: the repository has no trace
  semantics of the reference canonical ABI from which to derive it.

Note the different relations: the address-width bound is strict (`<`) because it comes from a
fixed-width integer; the lift check is non-strict (`≤`) because it compares with a maximum.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games
open Silmaril.Wasm.Game.Accept (Callout)
open Silmaril.Wasm.Component.WIT (ValType ClosedType)

/-- **The canonical-ABI correspondence of `accept(list<u8>)`, for a decoder `obs`** of the core
callout (`Callout.bytes32` for a 32-bit memory, `Callout.bytes64` for `memory64`). -/
structure CanonLowerAcceptBy {I X : Set FnName} (obs : Callout → Option (List UInt8))
    (callouts : Set Callout) (imp : String × String) (σ : Strategy (nsig I) (nsig X))
    (f : FnName) : Prop where
  /-- Every segment passed to the core import is passed as a list by the component. -/
  lower : ∀ o ∈ callouts, o.imp = imp → ∀ w, obs o = some w →
    ∃ s m, s ++ [m] ∈ σ.plays ∧ ∃ args, wev m = .req f args ∧ args1 bytes? args = some w
  /-- Every list the component passes is a segment passed to the core import. -/
  lift : ∀ s m, s ++ [m] ∈ σ.plays → ∀ args w, wev m = .req f args →
    args1 bytes? args = some w → ∃ o ∈ callouts, o.imp = imp ∧ obs o = some w

/-- The byte size of a `u8` list element (`1`, `Silmaril.Wasm.Component.WIT.layout_u8`). -/
def u8Size : Nat := (Silmaril.Wasm.Component.ABI.layout .i32 (.prim .u8 : ClosedType Empty)).size

/-- **Every list crossing the boundary passed the canonical ABI's length check** under the
limits `lim`: through the import `f` (`bytesLang`). -/
def ListLiftChecked {I X : Set FnName} (lim : Silmaril.Wasm.Component.Limits)
    (σ : Strategy (nsig I) (nsig X)) (f : FnName) : Prop :=
  ∀ w ∈ bytesLang σ f, w.length * u8Size ≤ lim.maxListBytes

/-- The same check for the lists passed to the export `f` (`exportBytesLang`). -/
def ExportListLiftChecked {I X : Set FnName} (lim : Silmaril.Wasm.Component.Limits)
    (σ : Strategy (nsig I) (nsig X)) (f : FnName) : Prop :=
  ∀ w ∈ exportBytesLang σ f, w.length * u8Size ≤ lim.maxListBytes

end Silmaril.Wasi.Accept
