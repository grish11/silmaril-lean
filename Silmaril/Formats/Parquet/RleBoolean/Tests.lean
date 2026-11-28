module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.RleBoolean.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.RleBoolean.Defs

/-! Independent multi-group V1/V2 BOOLEAN readback and a damaged later page. -/

namespace Silmaril.Formats.Parquet.RleBoolean

private def v1 : Bytes := ⟨include_bytes "../../../../data/parquet-rle-boolean/boolean-rle-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../data/parquet-rle-boolean/boolean-rle-v2.parquet"⟩
private def damaged : Bytes := ⟨include_bytes "../../../../data/parquet-rle-boolean/boolean-rle-v2-bad-length.parquet"⟩

private def first : List (Option Bool) :=
  List.replicate 8 (some true) ++ [some false, none, some true, some false, none, some true, none, some false]

private def middle : List (Option Bool) :=
  List.replicate 8 (some false) ++ [some true, none, some false, some true, none, some false, none, some true]

private def last : List (Option Bool) :=
  [some true, some false, some true, some false, none, some false, some true, none] ++ List.replicate 8 none

private def read (source : Bytes) (index : Nat) := readGroup {} source "enabled" index

#guard [0, 1, 2].mapM (read v1) = .ok [first, middle, last]
#guard [0, 1, 2].mapM (read v2) = .ok [first, middle, last]

#guard v2.data[126]! == 2 && damaged.data == v2.data.set! 126 3
#guard read damaged 1 = .error (.atPage 1 1 100 (.decode .lengthMismatch))
#guard [0, 2].mapM (read damaged) = .ok [first, last]

#guard read v2 3 = .error (.groupIndex 3)
#guard readGroup {} v2 "another" 0 = .error (.leafName "another" "enabled")
#guard v2.data[114]! == 6 && v2.data[250]! == 0
#guard read ⟨v2.data.set! 114 0⟩ 1 = .error (.atPage 1 1 100 (.encoding 0))
#guard read ⟨v2.data.set! 250 2⟩ 0 = .error (.column 0 (.codec 1))

-- Change the first Boolean length and lower the second page declaration
-- from eight slots to seven. The declared total fails before body decoding.
#guard v2.data[30]! == 2 && v2.data[44]! == 16 && v2.data[48]! == 16
#guard read ⟨v2.data.set! 30 3⟩ 0 = .error (.atPage 0 0 4 (.decode .lengthMismatch))
#guard read ⟨((v2.data.set! 30 3).set! 44 14).set! 48 14⟩ 0 = .error (.groupCount 0 16 15)

private def defaults : Limits := {}

#guard readGroup {defaults with maxFileBytes := 4} v2 "enabled" 0 = .error .fileByteLimit
#guard readGroup {defaults with maxRows := 15} v2 "enabled" 0 = .error (.rowLimit 0)
#guard readGroup {defaults with maxChunkBytes := 40} v2 "enabled" 0 = .error (.column 0 .byteLimit)
#guard readGroup {defaults with framing.maxPages := 1} v2 "enabled" 0 = .error (.column 0 (.framing .pageLimit))
#guard readGroup {defaults with decode.page.uncompressedBytes := 7} v2 "enabled" 0 =
  .error (.atPage 0 0 4 .byteLimit)
#guard readGroup {defaults with decode.page.levels.values := 7} v2 "enabled" 0 =
  .error (.atPage 0 0 4 .slotLimit)

end Silmaril.Formats.Parquet.RleBoolean
