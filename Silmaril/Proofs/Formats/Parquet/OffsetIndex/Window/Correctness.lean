module

public import Silmaril.Formats.Parquet.OffsetIndex.Window.Defs
import Silmaril.Formats.Parquet.OffsetIndex.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.OffsetIndex.Window

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.OffsetIndex (Entry Index Limits Error Partition)
open Silmaril.Formats.Parquet.OffsetIndex.Window

public theorem clip_some_iff {first stop : Nat} {page : Entry} {piece : Clip} :
    clip first stop page = some piece ↔
      piece = ⟨page, max first page.location.firstRow, min stop page.rowStop⟩ ∧
      max first page.location.firstRow < min stop page.rowStop := by
  by_cases nonempty : max first page.location.firstRow < min stop page.rowStop
  · simp [clip, nonempty, eq_comm]
  · simp [clip, nonempty]

public theorem clip_localBounds {first stop : Nat} {page : Entry} {piece : Clip}
    (h : clip first stop page = some piece) :
    piece.localBounds.1 < piece.localBounds.2 ∧
      piece.localBounds.2 ≤ page.rowStop - page.location.firstRow := by
  obtain ⟨rfl, nonempty⟩ := clip_some_iff.mp h
  simp only [Clip.localBounds]
  omega

private theorem entries_sublist (first stop : Nat) (pages : List Entry) :
    List.Sublist ((pages.filterMap (clip first stop)).map Clip.page) pages := by
  induction pages with
  | nil => exact .slnil
  | cons page pages ih =>
    cases intersection : clip first stop page with
    | none => simpa [List.filterMap_cons, intersection] using ih.cons page
    | some piece =>
      obtain ⟨rfl, _⟩ := clip_some_iff.mp intersection
      simpa [List.filterMap_cons, intersection] using ih.cons_cons page

public theorem plan_entries_sublist (first stop : Nat) (index : Index) :
    List.Sublist ((plan first stop index).map Clip.page) index.pages :=
  entries_sublist first stop index.pages

public theorem plan_rowOrder {index : Index} {groupRows : Nat}
    (checked : Partition 0 groupRows index.pages) (first stop : Nat) :
    (plan first stop index).Pairwise (fun a b => a.stop ≤ b.first) := by
  apply checked.ordered.filterMap (clip first stop)
  intro before after ordered a clippedA b clippedB
  obtain ⟨rfl, _⟩ := clip_some_iff.mp clippedA
  obtain ⟨rfl, _⟩ := clip_some_iff.mp clippedB
  exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans ordered.1 (Nat.le_max_right _ _))

public theorem plan_frameOrder {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat}
    {index : Index} {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    {chunk : Footer.Span} {bytes : Bytes}
    (checked : OffsetIndex.Evidence limits snapshot g c index group column chunk bytes)
    (first stop : Nat) :
    ((plan first stop index).map (fun piece => piece.page.frame)).Pairwise
      (fun a b => a.header.start < b.header.start) := by
  have ordered := Page.readChunk_payloads_disjoint checked.frames
  have bounded := Page.readChunk_payloads_bounded checked.frames
  have strict : (index.pages.map Entry.frame).Pairwise (fun a b => a.header.start < b.header.start) :=
    ordered.imp_of_mem fun {a b} memA _ between => by
      have within := bounded a memA
      have progress := within.headerProgress
      have adjacent := within.adjacent
      have width := within.payloadWidth
      show a.header.start < b.header.start
      omega
  have source := (plan_entries_sublist first stop index).map Entry.frame
  exact strict.sublist (by simpa only [List.map_map, Function.comp_def] using source)

private theorem count_plan (first stop row : Nat) (pages : List Entry) :
    (pages.filterMap (clip first stop)).countP
      (fun piece => decide (piece.first ≤ row ∧ row < piece.stop)) =
      if first ≤ row ∧ row < stop then
        pages.countP (fun p => decide (p.location.firstRow ≤ row ∧ row < p.rowStop))
      else 0 := by
  induction pages with
  | nil => simp
  | cons page pages ih =>
    have geometry : (max first page.location.firstRow ≤ row ∧ row < min stop page.rowStop) ↔
        (first ≤ row ∧ row < stop) ∧ (page.location.firstRow ≤ row ∧ row < page.rowStop) := by
      omega
    rw [List.filterMap_cons]
    by_cases overlap : max first page.location.firstRow < min stop page.rowStop
    · simp only [clip, ite_eq_left overlap, List.countP_cons, ih, decide_eq_true_eq, geometry]
      by_cases inWindow : first ≤ row ∧ row < stop <;> simp [inWindow]
    · have outside : ¬ ((first ≤ row ∧ row < stop) ∧ (page.location.firstRow ≤ row ∧ row < page.rowStop)) := by
        omega
      simp only [clip, ite_eq_right overlap, List.countP_cons, ih, decide_eq_true_eq]
      by_cases inWindow : first ≤ row ∧ row < stop
      · have notPage : ¬ (page.location.firstRow ≤ row ∧ row < page.rowStop) :=
          fun inside => outside ⟨inWindow, inside⟩
        simp [inWindow, notPage]
      · simp [inWindow]

public theorem plan_rowMultiplicity {index : Index} {groupRows : Nat}
    (checked : Partition 0 groupRows index.pages) (first stop row : Nat) :
    (plan first stop index).countP (fun piece => decide (piece.first ≤ row ∧ row < piece.stop)) =
      if first ≤ row ∧ row < min stop groupRows then 1 else 0 := by
  rw [plan, count_plan, checked.rowMultiplicity]
  by_cases window : first ≤ row ∧ row < stop
  · rw [ite_eq_left window]
    have equivalent : row < groupRows ↔ first ≤ row ∧ row < min stop groupRows := by omega
    simp only [Nat.zero_le, true_and, equivalent]
  · have outside : ¬ (first ≤ row ∧ row < min stop groupRows) := by omega
    rw [ite_eq_right window, ite_eq_right outside]

public theorem plan_empty_iff {index : Index} {groupRows first stop : Nat}
    (checked : Partition 0 groupRows index.pages) :
    plan first stop index = [] ↔ min stop groupRows ≤ first := by
  constructor
  · intro empty
    by_contra notEmpty
    have seen := plan_rowMultiplicity checked first stop first
    have inside : first ≤ first ∧ first < min stop groupRows := ⟨Nat.le_refl _, Nat.lt_of_not_ge notEmpty⟩
    rw [empty, ite_eq_left inside] at seen
    cases seen
  · intro upper
    cases result : plan first stop index with
    | nil => rfl
    | cons piece rest =>
      have member : piece ∈ index.pages.filterMap (clip first stop) := by
        rw [← plan, result]
        exact List.mem_cons_self
      obtain ⟨page, _, supported⟩ := List.mem_filterMap.mp member
      have positive : piece.first < piece.stop := by
        obtain ⟨rfl, nonempty⟩ := clip_some_iff.mp supported
        exact nonempty
      have seen := plan_rowMultiplicity checked first stop piece.first
      have outside : ¬ (first ≤ piece.first ∧ piece.first < min stop groupRows) := by omega
      simp only [ite_eq_right outside, List.countP_eq_zero] at seen
      exact (seen piece member (by simp [positive])).elim

public theorem planChecked_present {limits : Limits} {snapshot : Snapshot.Checked}
    {g c first stop : Nat} {pieces : List Clip}
    (h : planChecked limits snapshot g c first stop = .ok (some pieces)) :
    ∃ index group column chunk bytes,
      OffsetIndex.Evidence limits snapshot g c index group column chunk bytes ∧
      pieces = plan first stop index := by
  cases checked : OffsetIndex.validate limits snapshot g c with
  | error e => simp [planChecked, checked, Except.map] at h
  | ok index =>
    cases index with
    | none => simp [planChecked, checked, Except.map] at h
    | some index =>
      simp [planChecked, checked, Except.map] at h
      obtain ⟨group, column, chunk, bytes, evidence⟩ := OffsetIndex.validate_present checked
      exact ⟨index, group, column, chunk, bytes, evidence, h.symm⟩

public theorem planChecked_absent_iff {limits : Limits} {snapshot : Snapshot.Checked}
    {g c first stop : Nat} :
    planChecked limits snapshot g c first stop = .ok none ↔
      OffsetIndex.validate limits snapshot g c = .ok none := by
  cases checked : OffsetIndex.validate limits snapshot g c with
  | error e => simp [planChecked, checked, Except.map]
  | ok index => cases index <;> simp [planChecked, checked, Except.map]

public theorem planChecked_error_iff {limits : Limits} {snapshot : Snapshot.Checked}
    {g c first stop : Nat} {error : Error} :
    planChecked limits snapshot g c first stop = .error error ↔
      OffsetIndex.validate limits snapshot g c = .error error := by
  cases checked : OffsetIndex.validate limits snapshot g c <;> simp [planChecked, checked, Except.map]

end Silmaril.Proofs.Formats.Parquet.OffsetIndex.Window
