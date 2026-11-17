module

public import Silmaril.Wasm.Acceptor.Emit.Defs
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Component.Binary.Defs
import Silmaril.Proofs.Wasm.Acceptor.Emit

/-!
# The acceptor kit: the bytes of an acceptor component, results

Proofs in `Silmaril.Proofs.Wasm.Acceptor.Emit`. Each acceptor supplies three kernel
evaluations (`decide +kernel`): the core encoder succeeds on its module, the decoder succeeds
on the bytes, the component encoder succeeds on the emitted component.

* **`decode_coreBytesOf`**: then the core bytes decode to the module;
* **`parse_compBytes`**: then the component bytes parse to the emitted component.
-/

@[expose] public section

namespace Silmaril.Wasm.Acceptor

open Silmaril.Wasm
open Silmaril.Wasm.Component.Reference.ListLift (ListComp)

/-- **The core module bytes decode to the module.** -/
theorem decode_coreBytesOf {m : Module}
    (henc : (Binaryen.Exe.encodeModule? m).toOption.isSome = true)
    (hdec : (Binary.Core.decode? (coreBytesOf m)).isSome = true) :
    Binary.Core.decode? (coreBytesOf m) = some m :=
  Silmaril.Proofs.Wasm.Acceptor.decode_coreBytesOf henc hdec

/-- **The component bytes parse to the emitted component.** -/
theorem parse_compBytes {c : ListComp} {core : ByteArray}
    (h : (Silmaril.Wasm.Component.Binary.encode (c.toAst core)).isSome = true) :
    Silmaril.Wasm.Component.Binary.parse (compBytes c core) = .ok (c.toAst core) :=
  Silmaril.Proofs.Wasm.Acceptor.parse_compBytes h

end Silmaril.Wasm.Acceptor
