module

public import Silmaril.Wasm.Examples.SatAccept.Component.Defs
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# The SAT acceptor component: the bytes

`decode_coreBytes`: the core module bytes decode to `prog` (one kernel evaluation of the
decoder, `decode?_sound`, `encodeModule?_sound` and the functionality of the binary grammar).
`bytes_parse`: the component bytes parse to `satComp.toAst coreBytes` (one kernel evaluation
of the encoder and `parse_encode`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.SatAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Examples.SatAccept

set_option maxRecDepth 100000

theorem t_encodes : (Binaryen.Exe.encodeModule? prog).toOption.isSome = true := by decide +kernel

theorem t_decodes : (Binary.Core.decode? coreBytes).isSome = true := by decide +kernel

theorem t_encodeComp :
    (Silmaril.Wasm.Component.Binary.encode (satComp.toAst coreBytes)).isSome = true := by
  decide +kernel

/-- **The core module bytes decode to `prog`.** -/
theorem decode_coreBytes : Binary.Core.decode? coreBytes = some prog := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp t_decodes
  have hd := Binary.Core.decode?_sound hm
  cases he : Binaryen.Exe.encodeModule? prog with
  | error e =>
    have h := t_encodes
    simp [he, Except.toOption] at h
  | ok bs =>
    have hc : coreBytes = ⟨bs.toArray⟩ := by unfold coreBytes; rw [he]
    have hr := Binaryen.Exe.encodeModule?_sound he
    rw [hc] at hd
    rw [hm, Binary.Core.functional hd hr]

/-- **The component bytes parse to the emitted component.** -/
theorem bytes_parse :
    Silmaril.Wasm.Component.Binary.parse bytes = .ok (satComp.toAst coreBytes) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp t_encodeComp
  have hbytes : bytes = b := by unfold bytes; rw [hb]; rfl
  rw [hbytes]
  exact Silmaril.Wasm.Component.Binary.parse_encode hb

end Silmaril.Proofs.Wasm.Examples.SatAccept.Component
