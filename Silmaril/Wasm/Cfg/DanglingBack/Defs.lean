module

public import Silmaril.Wasm.Cfg.DanglingTyped.Thms

@[expose] public section

/-!
# The relaxed instance of the backward simulations' invariant (definitions)

`backD`: the relaxed invariant `DanglingTyped.ConfigOkD` (supported profile, `HeapBelow`, the
frame and code typed in context on a typing witness `gst s T X`) against store-keeping hosts with
typed values and unconstrained thrown addresses (`DanglingTyped.HostTypedD`) is an
`Interp.BackInv`. Every field is a theorem of `Silmaril.Wasm.Cfg.DanglingTyped.Thms`; the witness
is used only for typing facts that read no tag and no exception instance
(`Interp.CtxInv.wit`), and divergence through host-free steps is proved on the actual store
(`ConfigOkD.through`). The supported profile (no `ref.test`, `br_on_cast*`, aggregates, or
abstract-heap `ref.cast`) is part of `ConfigOkD`; it is what makes the witness's defined-type
casts decide as the actual store's.
-/

namespace Silmaril.Wasm.Cfg.DanglingBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Cfg.DanglingTyped

variable {H : Type}

/-- **The relaxed instance**: `ConfigOkD` against `HostTypedD` hosts. -/
def backD : Interp.BackInv H where
  CT := ConfigOkD
  suffix h := ConfigOkD.suffix h
  label h := ConfigOkD.label h
  handler h := ConfigOkD.handler h
  frame h := ConfigOkD.frameHole h
  step h hs := ConfigOkD.step h hs
  wit h := ConfigOkD.wit h
  HostOk := HostTypedD
  steps_host hT h hs := ConfigOkD.steps_host hT h hs
  hostOk_trap m hT := hostTypedD_trapAt m hT
  through h hK hd := ConfigOkD.through h hK hd

end Silmaril.Wasm.Cfg.DanglingBack
