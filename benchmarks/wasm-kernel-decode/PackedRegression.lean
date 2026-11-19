module

import Silmaril.Prelude.Bytes.Elab.Defs
public import Silmaril.Wasm.Binary.Packed.Thms

open Silmaril.Wasm.Binary.Packed

namespace WasmPackedRegression

kbytes_def good of_chunks 1 13 [0, 97, 115, 109, 1, 0, 0, 0, 0, 3, 128, 1, 7]
kbytes_def cut of_chunks 1 13 [0, 97, 115, 109, 1, 0, 0, 0, 0, 1, 128, 1, 0]
kbytes_def tooLong of_chunks 1 6 [128, 128, 128, 128, 128, 0]
kbytes_def unsignedOverflow of_chunks 1 5 [128, 128, 128, 128, 16]
kbytes_def signedOverflow of_chunks 1 5 [128, 128, 128, 128, 8]
kbytes_def badLength of_chunks 1 11 [0, 97, 115, 109, 1, 0, 0, 0, 1, 2, 0]

@[expose] public noncomputable def goodCursor : Cursor := ⟨good, good.wf_true, 0⟩

example : (readHeader.run goodCursor).map (·.2.pos) = .ok 8 := rfl

private def readSectionU32 : Reader (Except String (Nat × Nat)) := do
    readHeader
    let (_, payload) ← readSection
    pure ((readU 32).run payload |>.map (fun (value, next) => (value, next.pos)))

example : (readSectionU32.run goodCursor).map Prod.fst = .ok (.ok (128, 2)) := rfl

example : (readSectionU32.run ⟨cut, cut.wf_true, 0⟩).map (·.1.toOption) = .ok none := rfl

example : (readU 32 |>.run ⟨tooLong, tooLong.wf_true, 0⟩ |>.map Prod.fst) =
    .error "decoder: LEB128 too long" := rfl

example : (readU 32 |>.run ⟨unsignedOverflow, unsignedOverflow.wf_true, 0⟩ |>.map Prod.fst) =
    .error "decoder: LEB128 out of range" := rfl

example : (readS 32 |>.run ⟨signedOverflow, signedOverflow.wf_true, 0⟩ |>.map Prod.fst) =
    .error "decoder: signed LEB128 out of range" := rfl

example : (scanFrames.run ⟨badLength, badLength.wf_true, 0⟩).toOption = none := rfl

public theorem goodAgree : scanFramesSpec.run goodCursor.spec =
    .ok ([(0, 3)], { goodCursor.spec with pos := 13 }) :=
  scanFramesSpec_of_ok goodCursor [(0, 3)] 13 rfl

#print axioms goodAgree
#print axioms readSection_agrees
#print axioms readS_agrees

end WasmPackedRegression
