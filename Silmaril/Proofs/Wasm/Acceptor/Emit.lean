module

public import Silmaril.Wasm.Acceptor.Emit.Defs
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Component.Binary.Thms

@[expose] public section

/-!
# The acceptor kit: the bytes of an acceptor component (proofs)

`decode_coreBytesOf`: when the encoder succeeds on `m` and the decoder succeeds on its bytes,
the decoder answers `m` (`decode?_sound`, `encodeModule?_sound` and the functionality of the
binary grammar). `parse_compBytes`: when the component encoder succeeds, the bytes parse back
(`parse_encode`). The two success facts are the kernel evaluations each acceptor supplies.

A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Acceptor

open Silmaril.Wasm Silmaril.Wasm.Acceptor
open Silmaril.Wasm.Component.Reference.ListLift (ListComp)

theorem decode_coreBytesOf {m : Module}
    (henc : (Binaryen.Exe.encodeModule? m).toOption.isSome = true)
    (hdec : (Binary.Core.decode? (coreBytesOf m)).isSome = true) :
    Binary.Core.decode? (coreBytesOf m) = some m := by
  obtain ⟨m', hm⟩ := Option.isSome_iff_exists.mp hdec
  have hd := Binary.Core.decode?_sound hm
  cases he : Binaryen.Exe.encodeModule? m with
  | error e =>
    simp [he, Except.toOption] at henc
  | ok bs =>
    have hc : coreBytesOf m = ⟨bs.toArray⟩ := by unfold coreBytesOf; rw [he]
    have hr := Binaryen.Exe.encodeModule?_sound he
    rw [hc] at hd
    rw [hm, Binary.Core.functional hd hr]

theorem parse_compBytes {c : ListComp} {core : ByteArray}
    (h : (Silmaril.Wasm.Component.Binary.encode (c.toAst core)).isSome = true) :
    Silmaril.Wasm.Component.Binary.parse (compBytes c core) = .ok (c.toAst core) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  have hbytes : compBytes c core = b := by unfold compBytes; rw [hb]; rfl
  rw [hbytes]
  exact Silmaril.Wasm.Component.Binary.parse_encode hb

end Silmaril.Proofs.Wasm.Acceptor
