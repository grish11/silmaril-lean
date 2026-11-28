module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.FloatByteStreamSplit.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.FloatByteStreamSplit.Defs

/-! Full-file selection and raw words from independent PyArrow V1/V2 fixtures. -/

namespace Silmaril.Formats.Parquet.FloatByteStreamSplit

private def v1 : Bytes := ⟨include_bytes "../../../../data/parquet-float-byte-stream-split/float-bss-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../data/parquet-float-byte-stream-split/float-bss-v2.parquet"⟩

private def expected : List (List (Option UInt32)) :=
  [[some 0, none, some 0x80000000, some 0x7FC12345, some 1, some 0xFFC54321, some 0x7F800000, none],
   [some 0xFF800000, some 0x3F800000, none, some 0x80000001, some 0x00800000, none,
    some 0x7F7FFFFF, some 0x80400000],
   [some 0xBF800000, some 0x3F000001, none, some 0x7FC10001, none, none, none, none]]

private def read (source : Bytes) (index : Nat) := readGroup {} source "measurement" index

#guard ([0, 1, 2].mapM (read v1)) = .ok expected
#guard ([0, 1, 2].mapM (read v2)) = .ok expected
#guard read v2 3 = .error (.groupIndex 3)
#guard readGroup {} v2 "another" 0 = .error (.leafName "another" "measurement")

-- Field offsets use the encoded ZigZag integers in the original headers.
#guard v2.data[132]! == 18
#guard read ⟨v2.data.set! 132 0⟩ 1 = .error (.atPage 1 1 118 (.encoding 0))
#guard v2.data[285]! == 0
#guard read ⟨v2.data.set! 285 2⟩ 0 = .error (.columnCodec 0 1)

-- The V2 mask and null count agree after each edit. The unchanged 12
-- scalar bytes then disagree with the required four lanes.
#guard v2.data[14]! == 2 && v2.data[29]! == 13
private def short : Bytes := ⟨(v2.data.set! 14 0).set! 29 15⟩
private def surplus : Bytes := ⟨(v2.data.set! 14 4).set! 29 5⟩

#guard read short 0 = .error (.atPage 0 0 4 (.decode (.scalar .truncated)))
#guard read surplus 0 = .error (.atPage 0 0 4 (.decode (.scalar .trailingBytes)))

-- Make the second page declare three slots and rows. The preflight
-- rejects the group total before reaching the first page's short lanes.
#guard short.data[50]! == 8 && short.data[54]! == 8
#guard read ⟨(short.data.set! 50 6).set! 54 6⟩ 0 = .error (.groupCount 0 8 7)

private def defaults : Limits := {}

#guard readGroup {defaults with maxFileBytes := 4} v2 "measurement" 0 = .error .fileByteLimit
#guard readGroup {defaults with maxRows := 7} v2 "measurement" 0 = .error (.rowLimit 0)
#guard readGroup {defaults with maxChunkBytes := 20} v2 "measurement" 0 = .error (.chunkByteLimit 0)
#guard readGroup {defaults with framing.maxPages := 1} v2 "measurement" 0 = .error (.framing 0 .pageLimit)
#guard readGroup {defaults with decode.page.compressedBytes := 13} v2 "measurement" 0 =
  .error (.atPage 0 0 4 .compressedLimit)
#guard readGroup {defaults with decode.page.uncompressedBytes := 13} v2 "measurement" 0 =
  .error (.atPage 0 0 4 .outputLimit)
#guard readGroup {defaults with decode.page.levels.values := 3} v2 "measurement" 0 =
  .error (.atPage 0 0 4 .slotLimit)

end Silmaril.Formats.Parquet.FloatByteStreamSplit
