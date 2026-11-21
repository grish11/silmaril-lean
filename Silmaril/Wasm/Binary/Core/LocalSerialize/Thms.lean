module

public import Silmaril.Wasm.Binary.Core.LocalSerialize.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Thms
import Silmaril.Proofs.Wasm.Binary.Core.LocalSerialize

public section

namespace Silmaril.Wasm.Binary.Core.LocalSerialize

open Validation

/-- In this profile the decoder's locals cap and index validity imply both length bounds. -/
theorem Fits.of_bounds {locals index : Nat} (cap : locals ≤ Decode.maxLocals) (ref : index < locals) :
    Fits locals index := Proofs.Wasm.Binary.Core.LocalSerialize.fits_of_bounds cap ref

theorem Shape.localIndex_lt_decoderCap (shape : Shape) : shape.localIndex.toNat < Decode.maxLocals :=
  Nat.lt_of_lt_of_le shape.fits.resolves shape.fits.decoderCap

theorem erase_typed (shape : Shape) : (typed shape).erase = raw shape := rfl

theorem raw_sound (shape : Shape) : ModuleOk (raw shape) iface := (typed shape).sound

theorem decode_encode (shape : Shape) : Core.decode? (encode shape) = some (raw shape) :=
  Proofs.Wasm.Binary.Core.LocalSerialize.decode_encode shape

theorem raw_extract {mod : Wasm.Module} (fits : Serializable mod) : raw (extract mod fits) = mod :=
  Proofs.Wasm.Binary.Core.LocalSerialize.raw_extract fits

@[expose] def IntrinsicModule.toRaw (mod : IntrinsicModule) : RawModule :=
  ⟨⟨mod.val.erase, mod.val.sound⟩, mod.property⟩

theorem IntrinsicModule.encode_toRaw (mod : IntrinsicModule) : mod.toRaw.encode = mod.encode := rfl

theorem RawModule.roundtrip (mod : RawModule) : Core.decode? mod.encode = some mod.val.val :=
  (decode_encode _).trans (congrArg some (raw_extract mod.property))

theorem IntrinsicModule.roundtrip (mod : IntrinsicModule) : Core.decode? mod.encode = some mod.val.erase :=
  mod.toRaw.roundtrip

/-- Canonical reconstruction preserves the exact-erasure class, not the original witness. -/
theorem IntrinsicModule.reconstruct (mod : IntrinsicModule) :
    (Quot.mk _ (typed (extract mod.val.erase mod.property)) : Intrinsic.Module.Erasure iface) =
      Quot.mk _ mod.val := Quot.sound (raw_extract mod.property)

theorem decodeShape_encode (shape : Shape) : decodeShape? (encode shape) = some shape :=
  Proofs.Wasm.Binary.Core.LocalSerialize.decodeShape_encode shape

theorem decodeShape_sound {bytes : ByteArray} {shape : Shape} (ok : decodeShape? bytes = some shape) :
    Core.decode? bytes = some (raw shape) := Proofs.Wasm.Binary.Core.LocalSerialize.decodeShape_sound ok

theorem decodeIntrinsic_sound {bytes : ByteArray} {mod : IntrinsicModule}
    (ok : decodeIntrinsic? bytes = some mod) : Core.decode? bytes = some mod.val.erase := by
  obtain ⟨shape, decoded, rfl⟩ := Option.map_eq_some_iff.mp ok
  exact decodeShape_sound decoded

theorem decodeIntrinsic_roundtrip (mod : IntrinsicModule) :
    (decodeIntrinsic? mod.encode).map (fun decoded => (Quot.mk _ decoded.val : Intrinsic.Module.Erasure iface)) =
      some (Quot.mk _ mod.val) := by
  unfold decodeIntrinsic? IntrinsicModule.encode
  rw [decodeShape_encode]
  exact congrArg some mod.reconstruct

end Silmaril.Wasm.Binary.Core.LocalSerialize
