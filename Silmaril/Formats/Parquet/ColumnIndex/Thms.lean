module

public import Silmaril.Formats.Parquet.ColumnIndex.Defs
import Silmaril.Proofs.Formats.Parquet.ColumnIndex.Correctness

/-! Exact wire extent and ordinal binding to the same-file checked pages. -/

public section

namespace Silmaril.Formats.Parquet.ColumnIndex

theorem readExact_ok_iff {limits : Limits} {bytes : Bytes} {raw : Raw} :
    readExact limits bytes = .ok raw ↔ readPrefix limits bytes = .ok (raw, bytes.length) :=
  Proofs.Formats.Parquet.ColumnIndex.readExact_ok_iff

theorem readPrefix_stop {limits : Limits} {bytes : Bytes} {raw : Raw} {next : Nat}
    (h : readPrefix limits bytes = .ok (raw, next)) :
    ∃ stop, next = stop + 1 ∧ bytes.data[stop]? = some 0 :=
  Proofs.Formats.Parquet.ColumnIndex.readPrefix_stop h

/-- All wire fields align to the same page count, including bound widths and
any present null counts. -/
theorem checkShape_sound {raw : Raw} {pages : List OffsetIndex.Entry}
    (h : checkShape raw pages = .ok ()) : Aligned raw pages :=
  Proofs.Formats.Parquet.ColumnIndex.checkShape_sound h

/-- A present result gives the exact footer slice and the original framing
witness for this snapshot, group and selected column. -/
theorem validate_present {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat} {result : Index}
    (h : validate limits snapshot g c = .ok (some result)) :
    ∃ group column chunk offsetBytes bytes, Evidence limits snapshot g c result group column chunk offsetBytes bytes :=
  Proofs.Formats.Parquet.ColumnIndex.validate_present h

theorem validate_absent_iff {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat} :
    validate limits snapshot g c = .ok none ↔ ∃ group column,
      snapshot.groupAt g = some group ∧ group.columns[c]? = some column ∧
        column.columnIndexOffset = none ∧ column.columnIndexLength = none :=
  Proofs.Formats.Parquet.ColumnIndex.validate_absent_iff

/-- Pairing preserves every original checked entry and every claim in order. -/
theorem pages_aligned {index : Index} (aligned : Aligned index.raw index.offsetIndex.pages) :
    index.pages.map Prod.fst = index.offsetIndex.pages ∧ index.pages.map Prod.snd = index.raw.claims :=
  Proofs.Formats.Parquet.ColumnIndex.pages_aligned aligned

theorem readFile_ok_iff {limits : Limits} {source : Bytes} {g c : Nat} {result : Option Index} :
    readFile limits source g c = .ok result ↔ source.length ≤ limits.offsetIndex.maxFileBytes ∧
      ∃ snapshot, Snapshot.check (Failure := Unit) limits.offsetIndex.snapshot source = .ok snapshot ∧
        validate limits snapshot g c = .ok result :=
  Proofs.Formats.Parquet.ColumnIndex.readFile_ok_iff

end Silmaril.Formats.Parquet.ColumnIndex
