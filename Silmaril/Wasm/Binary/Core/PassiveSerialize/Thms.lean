module

public import Silmaril.Wasm.Binary.Core.PassiveSerialize.Defs
import Silmaril.Proofs.Wasm.Binary.Core.PassiveSerialize
public import Silmaril.Wasm.Validation.Intrinsic.Thms

public section

namespace Silmaril.Wasm.Binary.Core.PassiveSerialize

open Validation

namespace Reader

open Core.Decode
open Silmaril.Wasm.Tools.Meta (encU32)

theorem byte_at {bytes : ByteArray} {pos : Nat} {byte : UInt8} {tail : List UInt8}
    (rest : (Cursor.mk bytes pos).rest = byte :: tail) :
    readByte.run ⟨bytes, pos⟩ = .ok (byte, ⟨bytes, pos + 1⟩) :=
  Proofs.Wasm.Binary.Core.PassiveSerialize.byte_at rest

theorem u32_at {bytes : ByteArray} {pos number : Nat} {tail : List UInt8}
    (bound : number < 2 ^ 32) (rest : (Cursor.mk bytes pos).rest = encU32 number ++ tail) :
    (readU 32).run ⟨bytes, pos⟩ = .ok (number, ⟨bytes, pos + (encU32 number).length⟩) :=
  Proofs.Wasm.Binary.Core.PassiveSerialize.u32_at bound rest

theorem bytes_at {bytes : ByteArray} {pos : Nat} {part tail : List UInt8}
    (rest : (Cursor.mk bytes pos).rest = part ++ tail) (bound : pos ≤ bytes.size) :
    (readBytes part.length).run ⟨bytes, pos⟩ = .ok (part.toByteArray, ⟨bytes, pos + part.length⟩) :=
  Proofs.Wasm.Binary.Core.PassiveSerialize.bytes_at rest bound

end Reader

theorem raw_sound (bytes : ByteArray) : ModuleOk (raw bytes) iface := (typed bytes).sound

@[expose] def IntrinsicModule.toRaw (mod : IntrinsicModule) : RawModule :=
  ⟨⟨mod.val.erase, mod.val.sound⟩, mod.property⟩

theorem IntrinsicModule.encode_toRaw (mod : IntrinsicModule) : mod.toRaw.encode = mod.encode := rfl

theorem decode_encode (payload : Payload) : Core.decode? (encode payload) = some (raw payload.val) :=
  Proofs.Wasm.Binary.Core.PassiveSerialize.decode_encode payload

theorem raw_extract {mod : Wasm.Module} (fits : serializable mod) : raw (extract mod fits).val = mod :=
  Proofs.Wasm.Binary.Core.PassiveSerialize.raw_extract fits

theorem RawModule.roundtrip (mod : RawModule) : Core.decode? mod.encode = some mod.val.val :=
  (decode_encode _).trans (congrArg some (raw_extract mod.property))

theorem IntrinsicModule.roundtrip (mod : IntrinsicModule) : Core.decode? mod.encode = some mod.val.erase :=
  (decode_encode _).trans (congrArg some (raw_extract mod.property))

theorem decodePayload_encode (payload : Payload) : decodePayload? (encode payload) = some payload :=
  Proofs.Wasm.Binary.Core.PassiveSerialize.decodePayload_encode payload

theorem decodePayload_sound {source : ByteArray} {payload : Payload}
    (ok : decodePayload? source = some payload) : Core.decode? source = some (raw payload.val) :=
  Proofs.Wasm.Binary.Core.PassiveSerialize.decodePayload_sound ok

theorem decodeIntrinsic_sound {source : ByteArray} {mod : IntrinsicModule}
    (ok : decodeIntrinsic? source = some mod) : Core.decode? source = some mod.val.erase := by
  obtain ⟨payload, found, rfl⟩ := Option.map_eq_some_iff.mp ok
  exact decodePayload_sound found

theorem decodeIntrinsic_roundtrip (mod : IntrinsicModule) :
    (decodeIntrinsic? mod.encode).map (fun decoded => (Quot.mk _ decoded.val : Intrinsic.Module.Erasure iface)) =
      some (Quot.mk _ mod.val) :=
  Proofs.Wasm.Binary.Core.PassiveSerialize.decodeIntrinsic_roundtrip mod

end Silmaril.Wasm.Binary.Core.PassiveSerialize
