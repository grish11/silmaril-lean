module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.OffsetIndex.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.OffsetIndex.Defs

/-! Independently produced full files and malformed selected references and locations. -/

namespace Silmaril.Formats.Parquet.OffsetIndex

private def v1 : Bytes := ⟨include_bytes "../../../../data/parquet-offset-index/v1-index.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../data/parquet-offset-index/v2-index.parquet"⟩
private def noIndex : Bytes := ⟨include_bytes "../../../../data/parquet-offset-index/v1-no-index.parquet"⟩

private def summary (result : Index) : Footer.Span × List (Location × Nat) :=
  (result.span, result.pages.map fun page => (page.location, page.rowStop))

private def fixture (source : Bytes) (group : Nat) :
    Except Error (Option (Footer.Span × List (Location × Nat))) :=
  (readFile {} source group 0).map (·.map summary)

#guard fixture v1 0 = .ok (some (⟨328, 353⟩, [(⟨4, 35, 0⟩, 4), (⟨39, 35, 4⟩, 8), (⟨74, 35, 8⟩, 12)]))
#guard fixture v1 1 = .ok (some (⟨353, 380⟩, [(⟨109, 35, 0⟩, 4), (⟨144, 39, 4⟩, 8), (⟨183, 35, 8⟩, 12)]))
#guard fixture v2 0 = .ok (some (⟨334, 359⟩, [(⟨4, 36, 0⟩, 4), (⟨40, 36, 4⟩, 8), (⟨76, 36, 8⟩, 12)]))
#guard fixture v2 1 = .ok (some (⟨359, 386⟩, [(⟨112, 36, 0⟩, 4), (⟨148, 40, 4⟩, 8), (⟨188, 36, 8⟩, 12)]))
#guard fixture noIndex 0 = .ok none
#guard fixture noIndex 1 = .ok none
#guard readFile {} v1 2 0 = .error (.groupIndex 2)
#guard readFile {} v1 0 1 = .error (.columnIndex 1)

private def change (source : Bytes) (offset : Nat) (byte : UInt8) : Bytes :=
  ⟨source.data.set! offset byte⟩

-- Mutate the actual index and frame in the first row group.
#guard fixture (change v1 331 10) 0 = .error (.pageOffset 0 5 4)
#guard fixture (change v1 333 72) 0 = .error (.pageSize 0 36 35)
#guard fixture (change v1 342 0) 0 = .error (.firstRow 1 0 4)
#guard fixture (change v1 82 6) 0 = .error (.rowCount 12 11)
#guard fixture (change v1 331 1) 0 = .error (.invalidLocationField 1)
#guard fixture (change v1 333 0) 0 = .error (.invalidLocationField 2)
#guard fixture (change v1 335 1) 0 = .error (.invalidLocationField 3)

-- A bad definition length in the page body does not affect index validation.
#guard fixture (change v1 21 0xff) 0 = fixture v1 0
#guard fixture (change noIndex 4 0xff) 0 = .ok none

-- Advertise too few or too many index bytes in the original footer.
#guard fixture (change v1 498 48) 0 = .error (.compact (.compact .truncated))
#guard fixture (change v1 498 52) 0 = .error .trailingIndexBytes
#guard fixture (change v1 498 0) 0 = .error (.snapshot (.invalidMetadata .indexInterval))

-- Redirect the first reference to the second group's valid index.
#guard fixture (change (change v1 495 0xc2) 498 54) 0 = .error (.pageOffset 0 109 4)
#guard fixture (change (change v1 495 0x88) 496 1) 0 = .error .indexOverlapsChunk

-- Drop ColumnChunk field 5, adjust the delta to field 6 and shorten the footer.
private def partialRef : Bytes :=
  (Footer.fileBytes v1 0 497).append <|
    (Bytes.ofList [0x26]).append <|
      (Footer.fileBytes v1 500 864).append (Bytes.ofList [0xe2, 1, 0, 0, 0x50, 0x41, 0x52, 0x31])

#guard fixture partialRef 0 = .error (.snapshot (.invalidMetadata .indexInterval))

private def tight : Limits where
  maxFileBytes := 872
  maxRows := 12
  maxIndexBytes := 25
  maxChunkBytes := 105
  maxLocations := 3
  page := { maxPages := 3 }

#guard readFile tight v1 0 0 = readFile {} v1 0 0
#guard readFile { maxFileBytes := 871 } v1 0 0 = .error .fileByteLimit
#guard readFile { maxRows := 11 } v1 0 0 = .error .rowLimit
#guard readFile { maxIndexBytes := 24 } v1 0 0 = .error .indexByteLimit
#guard readFile { maxChunkBytes := 104 } v1 0 0 = .error .chunkByteLimit
#guard readFile { page := { maxPages := 2 } } v1 0 0 = .error (.page .pageLimit)
#guard readFile { maxLocations := 2 } v1 0 0 = .error (.compact (.compact .lengthLimit))

private def framed (kind : Page.Kind) : Page.Frame :=
  ⟨⟨0, 0, none, kind⟩, ⟨4, 10⟩, ⟨10, 10⟩⟩

#guard matchPages 1 [] [framed (.dataV1 ⟨1, 0, 3, 3⟩)] = .error .locationCount
#guard matchPages 0 [⟨4, 6, 0⟩] [framed (.dataV1 ⟨0, 0, 3, 3⟩)] = .error (.invalidPageRows 0)
#guard matchPages 1 [⟨4, 6, 0⟩] [framed (.dataV2 ⟨2, 0, 1, 0, 0, 0, false⟩)] =
  .error (.invalidPageRows 0)
#guard matchPages 1 [⟨4, 6, 0⟩] [framed (.dataV2 ⟨1, 0, 1, 0, 0, 1, false⟩)] =
  .error (.invalidPageRows 0)
#guard matchPages 1 [⟨4, 6, 0⟩] [framed (.dictionary ⟨1, 0, none⟩)] = .error (.unsupportedPage 0)

end Silmaril.Formats.Parquet.OffsetIndex
