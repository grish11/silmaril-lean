module

public import Silmaril.Formats.Parquet.OffsetIndex.Window.Defs
import Silmaril.Proofs.Formats.Parquet.OffsetIndex.Window.Correctness

/-! Exact row-window coverage and ordered preservation of the original frames. -/

public section

namespace Silmaril.Formats.Parquet.OffsetIndex.Window

theorem clip_some_iff {first stop : Nat} {page : Entry} {piece : Clip} :
    clip first stop page = some piece ↔
      piece = ⟨page, max first page.location.firstRow, min stop page.rowStop⟩ ∧
      max first page.location.firstRow < min stop page.rowStop :=
  Proofs.Formats.Parquet.OffsetIndex.Window.clip_some_iff

theorem clip_localBounds {first stop : Nat} {page : Entry} {piece : Clip}
    (h : clip first stop page = some piece) :
    piece.localBounds.1 < piece.localBounds.2 ∧
      piece.localBounds.2 ≤ page.rowStop - page.location.firstRow :=
  Proofs.Formats.Parquet.OffsetIndex.Window.clip_localBounds h

/-- The returned entries are an ordered subsequence of the original entries,
including their original frames. -/
theorem plan_entries_sublist (first stop : Nat) (index : Index) :
    List.Sublist ((plan first stop index).map Clip.page) index.pages :=
  Proofs.Formats.Parquet.OffsetIndex.Window.plan_entries_sublist first stop index

theorem plan_rowOrder {index : Index} {groupRows : Nat}
    (checked : Partition 0 groupRows index.pages) (first stop : Nat) :
    (plan first stop index).Pairwise (fun a b => a.stop ≤ b.first) :=
  Proofs.Formats.Parquet.OffsetIndex.Window.plan_rowOrder checked first stop

/-- In a checked file, clipped frames keep their strict on-disk header order. -/
theorem plan_frameOrder {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat}
    {index : Index} {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    {chunk : Footer.Span} {bytes : Bytes}
    (checked : OffsetIndex.Evidence limits snapshot g c index group column chunk bytes)
    (first stop : Nat) :
    ((plan first stop index).map (fun piece => piece.page.frame)).Pairwise
      (fun a b => a.header.start < b.header.start) :=
  Proofs.Formats.Parquet.OffsetIndex.Window.plan_frameOrder checked first stop

theorem plan_frames_nodup {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat}
    {index : Index} {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    {chunk : Footer.Span} {bytes : Bytes}
    (checked : OffsetIndex.Evidence limits snapshot g c index group column chunk bytes)
    (first stop : Nat) :
    ((plan first stop index).map (fun piece => piece.page.frame)).Nodup :=
  (plan_frameOrder checked first stop).imp (S := fun (a b : Page.Frame) => a ≠ b)
    (fun order equal => Nat.ne_of_lt order (congrArg (fun frame : Page.Frame => frame.header.start) equal))

/-- Each row in the intersection of the window and the checked group lies
in exactly one clip. All other rows lie in zero clips. -/
theorem plan_rowMultiplicity {index : Index} {groupRows : Nat}
    (checked : Partition 0 groupRows index.pages) (first stop row : Nat) :
    (plan first stop index).countP (fun piece => decide (piece.first ≤ row ∧ row < piece.stop)) =
      if first ≤ row ∧ row < min stop groupRows then 1 else 0 :=
  Proofs.Formats.Parquet.OffsetIndex.Window.plan_rowMultiplicity checked first stop row

theorem plan_empty_iff {index : Index} {groupRows first stop : Nat}
    (checked : Partition 0 groupRows index.pages) :
    plan first stop index = [] ↔ min stop groupRows ≤ first :=
  Proofs.Formats.Parquet.OffsetIndex.Window.plan_empty_iff checked

/-- A present plan has the checked index for this same snapshot and selected
column, with the plan computed from exactly those original entries. -/
theorem planChecked_present {limits : Limits} {snapshot : Snapshot.Checked}
    {g c first stop : Nat} {pieces : List Clip}
    (h : planChecked limits snapshot g c first stop = .ok (some pieces)) :
    ∃ index group column chunk bytes,
      OffsetIndex.Evidence limits snapshot g c index group column chunk bytes ∧
      pieces = plan first stop index :=
  Proofs.Formats.Parquet.OffsetIndex.Window.planChecked_present h

theorem planChecked_absent_iff {limits : Limits} {snapshot : Snapshot.Checked}
    {g c first stop : Nat} :
    planChecked limits snapshot g c first stop = .ok none ↔
      OffsetIndex.validate limits snapshot g c = .ok none :=
  Proofs.Formats.Parquet.OffsetIndex.Window.planChecked_absent_iff

theorem planChecked_error_iff {limits : Limits} {snapshot : Snapshot.Checked}
    {g c first stop : Nat} {error : Error} :
    planChecked limits snapshot g c first stop = .error error ↔
      OffsetIndex.validate limits snapshot g c = .error error :=
  Proofs.Formats.Parquet.OffsetIndex.Window.planChecked_error_iff

end Silmaril.Formats.Parquet.OffsetIndex.Window
