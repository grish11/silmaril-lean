module

public import Silmaril.Wasm.Component.ChunkedDecode.Defs
public import Silmaril.Raw.Wasm.Component.ChunkedDecode.Slices
import Silmaril.Proofs.Wasm.Component.ChunkedDecode.Bounded

/-!
# Chunked decode certificates give `decode?` itself

The chunked certificates of `Silmaril.Wasm.Component.Chunked` run silmaril's core readers on slices
of a file (sections, code groups, instruction plans) and prove the grammar `Encodes`. This topic
proves that the same checks give the **decoder's own result**, `decode? (arr bytes) = some m`, so
that `BinaryP3.parseStrict` (whose core-module rule is `decode?`) can be proved on files of
hundreds of KB to MB without running `decode?` on the whole file in the kernel (a list-backed
`ByteArray` costs time linear in the position at each read).

**PROVED** (raw proofs in `Silmaril.Raw.Wasm.Component.ChunkedDecode.{Frame,Plans,Module,Slices}`):

* `Frame p` for every reader `decode?` uses: what a reader does on an input it does inside any
  larger input (`run_of_runAll`); `readSeq`/`readInstr` are monotone in their fuel
  (`readSeq_mono`); positions only move forward (`Mono`);
* pieces checked separately are one vector run (`readVec_go_of_chkSeq`, `readVec_of_chkVec'`,
  counts bounded by the bytes), instruction plans are `readSeq` runs (`readSeq_of_chkI`), code
  entry plans are `readCode` runs given `chkLocals` (`readCode_of_chkCode`, `codes_seg_of_ok`),
  data plans are `readData` runs (`datas_seg`);
* sections, the code section, the data section and custom sections are steps of
  `readModule.go` (`go_vec_s`, `go_code_s`, `go_data_s`, `go_custom_s`, `go_end_s`), and
  `decode_s` gives `decode?` of a module that is a slice of a file from a run of that loop.

A Silmaril addition.
-/

public section

namespace Silmaril.Wasm.Component.ChunkedDecode

open Silmaril.Wasm.Binary.Core.Decode

theorem readHeader_frame : Frame readHeader :=
  Proofs.Wasm.Component.ChunkedDecode.readHeader_frame

theorem readSectionBody_frame (id : Nat) (sections : Sections) :
    Frame (readSectionBody id sections) :=
  Proofs.Wasm.Component.ChunkedDecode.readSectionBody_frame id sections

end Silmaril.Wasm.Component.ChunkedDecode
