module

public import Silmaril.Wasm.Binary.Packed.Defs
import Silmaril.Proofs.Wasm.Binary.Packed.Sim

public section

namespace Silmaril.Wasm.Binary.Packed

theorem Cursor.spec_size (cursor : Cursor) : cursor.spec.bytes.size = cursor.source.len :=
  Proofs.Wasm.Binary.Packed.size cursor

theorem readByte_agrees : Agrees id readByte Core.Decode.readByte :=
  Proofs.Wasm.Binary.Packed.readByte_agrees

theorem remaining_agrees : Agrees id remaining Core.Decode.remaining :=
  Proofs.Wasm.Binary.Packed.remaining_agrees

theorem readSlice_agrees (width : Nat) :
    Agrees (fun payload => payload.source.toByteArray) (readSlice width) (Core.Decode.readBytes width) :=
  Proofs.Wasm.Binary.Packed.readSlice_agrees width

theorem readU_agrees (bits : Nat) : Agrees id (readU bits) (Core.Decode.readU bits) :=
  Proofs.Wasm.Binary.Packed.readU_agrees bits

theorem readS_agrees (bits : Nat) : Agrees id (readS bits) (Core.Decode.readS bits) :=
  Proofs.Wasm.Binary.Packed.readS_agrees bits

theorem readHeader_agrees : Agrees id readHeader Core.Decode.readHeader :=
  Proofs.Wasm.Binary.Packed.readHeader_agrees

theorem readSection_agrees :
    Agrees (fun (id, payload) => (id, payload.source.toByteArray)) readSection readSectionSpec :=
  Proofs.Wasm.Binary.Packed.readSection_agrees

theorem scanFrames_agrees : Agrees id scanFrames scanFramesSpec :=
  Proofs.Wasm.Binary.Packed.scanFrames_agrees

/-- Use a kernel-checked packed computation to prove the exact reference framing result. -/
theorem scanFramesSpec_of_ok (cursor : Cursor) (frames : List (Nat × Nat)) (finish : Nat)
    (check : scanFrames.run cursor = .ok (frames, { cursor with pos := finish })) :
    scanFramesSpec.run cursor.spec = .ok (frames, { cursor.spec with pos := finish }) :=
  (scanFrames_agrees cursor).symm.trans (congrArg (Except.map _) check)

end Silmaril.Wasm.Binary.Packed
