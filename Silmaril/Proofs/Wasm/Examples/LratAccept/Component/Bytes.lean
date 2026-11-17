module

public import Silmaril.Wasm.Examples.LratAccept.Component.Defs
public import Silmaril.Wasm.Acceptor.Emit.Thms

/-!
# The LRAT acceptor component: the bytes

`decode_coreBytes`: the core module bytes decode to `prog`; `bytes_parse`: the component bytes
parse to `lratComp.toAst coreBytes`. Each is the acceptor kit's combinator
(`Silmaril.Wasm.Acceptor.decode_coreBytesOf`, `parse_compBytes`) on kernel evaluations of the
encoders and the decoder.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.LratAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Examples.LratAccept

set_option maxRecDepth 100000

theorem t_encodes : (Binaryen.Exe.encodeModule? prog).toOption.isSome = true := by decide +kernel

-- The decoder run on the 3 KiB module exceeds the default heartbeat budget of the kernel check.
set_option maxHeartbeats 0 in
theorem t_decodes : (Binary.Core.decode? coreBytes).isSome = true := by decide +kernel

theorem t_encodeComp :
    (Silmaril.Wasm.Component.Binary.encode (lratComp.toAst coreBytes)).isSome = true := by
  decide +kernel

/-- **The core module bytes decode to `prog`.** -/
theorem decode_coreBytes : Binary.Core.decode? coreBytes = some prog :=
  Silmaril.Wasm.Acceptor.decode_coreBytesOf t_encodes t_decodes

/-- **The component bytes parse to the emitted component.** -/
theorem bytes_parse :
    Silmaril.Wasm.Component.Binary.parse bytes = .ok (lratComp.toAst coreBytes) :=
  Silmaril.Wasm.Acceptor.parse_compBytes t_encodeComp

end Silmaril.Proofs.Wasm.Examples.LratAccept.Component
