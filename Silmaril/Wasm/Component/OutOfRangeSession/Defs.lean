module

public import Silmaril.Wasm.Component.OutOfRange.Defs
public import Silmaril.Wasm.Component.ExtSession.Defs

/-!
# Session nodes on `sigU`: definitions

* `IsTrapS m n`: the answer `n` to a call `m` at the session interface `sigS` is the trap
  `.inr ()` (the session view of `none`).
* `ofSession σ`: a session strategy `σ : DStrategy sigS sigS` seen on `sigU`, its answers
  relabelled by `toU` above and the answers it receives by `ofU` below, as in
  `Silmaril.Wasm.Component.ExtSession`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

/-- The trap answers at the session interface. -/
def IsTrapS (_ : sigS.Op) (n : Payload ⊕ PUnit.{1}) : Prop := n = .inr PUnit.unit

/-- A session strategy seen on `sigU`. -/
def ofSession (σ : DStrategy sigS sigS) : DStrategy sigU sigU :=
  (DStrategy.ofHandler ofU).comp (σ.comp (DStrategy.ofHandler toU))

end Silmaril.Wasm.Component
