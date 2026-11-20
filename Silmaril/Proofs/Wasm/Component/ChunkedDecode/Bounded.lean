module

public import Silmaril.Raw.Wasm.Component.ChunkedDecode.Module

public section

namespace Silmaril.Proofs.Wasm.Component.ChunkedDecode

open Silmaril.Wasm.Binary.Core.Decode Silmaril.Wasm.Component.ChunkedDecode

theorem readHeader_frame : Frame readHeader := by
  unfold readHeader
  frame_tac

theorem readSectionBody_frame (id : Nat) (sections : Sections) :
    Frame (readSectionBody id sections) := by
  unfold readSectionBody
  split <;> first
    | exact frame_decodeError _
    | apply frame_bind
      · first
        | exact frame_readIdx
        | exact frame_readU _
        | apply frame_readVec
          first | exact frame_readRecType | exact frame_readImport | exact frame_readIdx
                | exact frame_readTable | exact frame_readMemType | exact frame_readGlobal
                | exact frame_readExport | exact frame_readElem | exact frame_readCode
                | exact frame_readData | exact frame_readTag
      · intro; exact frame_pure _

end Silmaril.Proofs.Wasm.Component.ChunkedDecode
