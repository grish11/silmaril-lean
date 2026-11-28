module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.OffsetIndex.Window.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.OffsetIndex.Window.Defs

/-! Pinned full-file V2 Snappy windows and the absent-index boundary. -/

namespace Silmaril.Formats.Parquet.OffsetIndex.Window

private def indexed : Bytes := ⟨include_bytes "../../../../../data/parquet-offset-index/v2-index.parquet"⟩
private def unindexed : Bytes := ⟨include_bytes "../../../../../data/parquet-offset-index/v1-no-index.parquet"⟩

private def check (source : Bytes) (group first stop : Nat) : Except Error (Option (List Clip)) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).mapError .snapshot
  planChecked {} snapshot group 0 first stop

private def observed (first stop : Nat) :
    Except Error (Option (List (Nat × Nat × Nat × Nat))) :=
  (check indexed 1 first stop).map (Option.map (List.map fun piece =>
    (piece.page.frame.header.start, piece.page.location.compressedSize, piece.localBounds.1, piece.localBounds.2)))

-- The tuple is (original frame offset, header-inclusive size, local start, local stop).
#guard observed 3 10 = .ok (some [(112, 36, 3, 4), (148, 40, 0, 4), (188, 36, 0, 2)])
#guard observed 4 8 = .ok (some [(148, 40, 0, 4)])
#guard observed 10 15 = .ok (some [(188, 36, 2, 4)])
#guard observed 0 15 = .ok (some [(112, 36, 0, 4), (148, 40, 0, 4), (188, 36, 0, 4)])
#guard observed 0 0 = .ok (some [])
#guard observed 8 4 = .ok (some [])
#guard observed 12 15 = .ok (some [])
#guard observed 13 15 = .ok (some [])
#guard check unindexed 1 3 10 = .ok none
#guard check unindexed 1 0 0 = .ok none

-- Change the first indexed offset in group 1 from 112 to 113.
private def badIndex : Bytes := ⟨indexed.data.set! 362 0xe2⟩

#guard check badIndex 1 3 10 = .error (.pageOffset 0 113 112)
#guard check badIndex 1 0 0 = .error (.pageOffset 0 113 112)
#guard check indexed 2 0 0 = .error (.groupIndex 2)

end Silmaril.Formats.Parquet.OffsetIndex.Window
