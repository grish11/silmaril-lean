module

public import Silmaril.Wasi.Component.Accept.Defs
public import Silmaril.Wasm.Game.Accept.Defs

/-! # Module and component acceptance through the canonical ABI: the correspondence

A component that imports `accept: func(list<u8>)` and is implemented by a core module reaches
the host through `canon lower`: the core module imports a function of type
`(i32, i32) -> ()` (`Silmaril.Wasm.Component.WIT.flattenFunc_accept_import`) and passes the
list as `(ptr, len)` in its memory, one byte per element
(`Silmaril.Wasm.Component.WIT.layout_u8`, `Silmaril.Wasm.Game.Accept.Callout.getElem?_of_segment`).

`CanonLowerAccept callouts imp σ f` is the correspondence that a canonical-ABI adapter must
establish between the module's callouts to its core import `imp` (`Callout.bytes32`) and the
component's calls to its WIT import `f`: each segment passed to the core import is passed as a
`list<u8>` by some play of the component, and each list the component passes is a segment some
callout passes. It is a hypothesis, not a theorem: the repository's IR components
(`Silmaril.Wasm.Component.Comp`) have no list values and no memory lowering, and the reference
canonical ABI (`Silmaril.Wasm.Component.Canon`) has no trace semantics to compare with, so
the correspondence is not derived here for any adapter. Given it, module and component accept
the same bytes (`Silmaril.Wasi.Accept.bytesLang_eq_of_canonLowerAccept`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games
open Silmaril.Wasm.Game.Accept (Callout)

/-- **The canonical-ABI correspondence of `accept(list<u8>)`**: core callouts to `imp`
observing a segment match component calls to `f` passing those bytes, both ways. -/
structure CanonLowerAccept {I X : Set FnName} (callouts : Set Callout) (imp : String × String)
    (σ : Strategy (nsig I) (nsig X)) (f : FnName) : Prop where
  /-- Every segment passed to the core import is passed as a list by the component. -/
  lower : ∀ o ∈ callouts, o.imp = imp → ∀ w, o.bytes32 = some w →
    ∃ s m, s ++ [m] ∈ σ.plays ∧ ∃ args, wev m = .req f args ∧ args1 bytes? args = some w
  /-- Every list the component passes is a segment passed to the core import. -/
  lift : ∀ s m, s ++ [m] ∈ σ.plays → ∀ args w, wev m = .req f args →
    args1 bytes? args = some w → ∃ o ∈ callouts, o.imp = imp ∧ o.bytes32 = some w

end Silmaril.Wasi.Accept
