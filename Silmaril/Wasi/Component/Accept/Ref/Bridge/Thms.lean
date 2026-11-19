module

public import Silmaril.Wasi.Component.Accept.Ref.Typed.Defs
public import Silmaril.Wasi.Component.Accept.Defs
public import Silmaril.Wasm.Component.Reference.Bridge.Defs
import Silmaril.Proofs.Wasi.Component.Accept.RefBridge

/-! # REF and the component IR read `accept`'s bytes the same way

The component IR reads the bytes of an `accept` call with `Silmaril.Wasi.Accept.bytes?` on IR
values. The reference machine (REF) reads them with `Ref.bytesOf?` on REF values. IR values
map to REF values by `Reference.toRefVal`, the value map of the IR→REF bridge
(`Reference.Bridge`). Under that map the two readings agree on every value:

* `bytesOf?_toRefVal`: `bytesOf? [toRefVal v] = bytes? v`;
* `u8Of?_toRefVal`: the byte of a `u8` component value, likewise.

This is prerequisite (P2) of the tuple-acceptor bridge (`docs/projects/component-caveats.md`).
It is about values only. Relating whole acceptance (REF runs to IR plays) still needs (P3), an
execution-based core semantics for lowered modules, and (P4), REF↔IR adequacy with imports.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Wasm.Component.Reference (toRefVal)

theorem u8Of?_toRefVal (v : Silmaril.Wasm.Component.Val) :
    u8Of? (toRefVal v) = Silmaril.Wasi.Accept.decodePrim .u8 v :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.u8Of?_toRefVal v

theorem bytesOf?_toRefVal (v : Silmaril.Wasm.Component.Val) :
    bytesOf? [toRefVal v] = Silmaril.Wasi.Accept.bytes? v :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.bytesOf?_toRefVal v

end Silmaril.Wasi.Accept.Ref
