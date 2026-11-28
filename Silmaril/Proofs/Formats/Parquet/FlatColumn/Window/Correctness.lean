module

public import Silmaril.Formats.Parquet.FlatColumn.Window.Defs
import Silmaril.Formats.Parquet.FlatColumn.Thms
import Silmaril.Formats.Parquet.OffsetIndex.Window.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.FlatColumn.Window

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.FlatColumn
open Silmaril.Formats.Parquet.FlatColumn.Window

public theorem read_error_iff
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy}
    {decode : DecodePage α ε} {indexLimits : OffsetIndex.Limits}
    {group first stop : Nat} {error : Error ε} :
    FlatColumn.Window.read binding limits policy decode indexLimits group first stop = .error error ↔
      readColumn binding limits policy decode group = .error error := by
  cases full : readColumn binding limits policy decode group <;>
    simp [FlatColumn.Window.read, full, bind, Except.bind, pure, Except.pure]

public theorem read_rows
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    (binding : Binding snapshot selection) (limits : Limits) (policy : Policy)
    (decode : DecodePage α ε) (indexLimits : OffsetIndex.Limits) (group first stop : Nat) :
    (FlatColumn.Window.read binding limits policy decode indexLimits group first stop).map Result.rows =
      (readColumn binding limits policy decode group).map (sliceRows first stop) := by
  cases full : readColumn binding limits policy decode group <;>
    simp [FlatColumn.Window.read, full, bind, Except.bind, pure, Except.pure, Except.map]

public theorem read_ok_iff
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy}
    {decode : DecodePage α ε} {indexLimits : OffsetIndex.Limits}
    {group first stop : Nat} {result : Result α} :
    FlatColumn.Window.read binding limits policy decode indexLimits group first stop = .ok result ↔
      ∃ slots, readColumn binding limits policy decode group = .ok slots ∧
        result.rows = sliceRows first stop slots ∧
        result.indexPlan = OffsetIndex.Window.planChecked { indexLimits with page := limits.framing }
          snapshot group binding.columnOrdinal first stop := by
  cases full : readColumn binding limits policy decode group with
  | error error => simp [FlatColumn.Window.read, full, bind, Except.bind]
  | ok slots =>
    cases result
    simp [FlatColumn.Window.read, full, bind, Except.bind, pure, Except.pure, eq_comm]

public theorem read_length
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy}
    {decode : DecodePage α ε} {indexLimits : OffsetIndex.Limits}
    {group first stop : Nat} {result : Result α}
    (h : FlatColumn.Window.read binding limits policy decode indexLimits group first stop = .ok result) :
    ∃ selected, snapshot.groupAt group = some selected ∧
      result.rows.length = min stop selected.numRows.toNat - first := by
  obtain ⟨slots, full, sliced, _⟩ := read_ok_iff.mp h
  obtain ⟨selected, _, _, _, _, groupAt, _, _, _, _, _, _, _, _, _, _, length⟩ := readColumn_wire full
  refine ⟨selected, groupAt, ?_⟩
  rw [sliced, sliceRows, List.length_take, List.length_drop, length]
  omega

private theorem sameColumnFrames
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {decode : DecodePage α ε}
    {indexLimits : OffsetIndex.Limits} {groupOrdinal : Nat}
    {index : OffsetIndex.Index} {group indexGroup : Footer.RowGroup} {indexColumn : Footer.ColumnChunk}
    {indexChunk : Footer.Span} {bytes : Bytes} {slots : List (Option α)}
    (readWire : ColumnWire binding limits decode groupOrdinal group slots)
    (indexed : OffsetIndex.Evidence indexLimits snapshot groupOrdinal binding.columnOrdinal
      index indexGroup indexColumn indexChunk bytes)
    (sameLimits : indexLimits.page = limits.framing) :
    ∃ pages, List.Forall₂ (CallbackWire decode binding.leaf indexColumn.metadata snapshot.bytes)
      (index.pages.map OffsetIndex.Entry.frame) pages ∧ slots = pages.flatten := by
  obtain ⟨column, chunk, frames, pages, groupAt, columnAt, _, _, _, _, span, framed, _, decoded, flatten, _⟩ :=
    readWire
  have groupEq := Option.some.inj (groupAt.symm.trans indexed.selected.groupAt)
  subst indexGroup
  have columnEq := Option.some.inj (columnAt.symm.trans indexed.selected.columnAt)
  subst indexColumn
  have spanEq := Option.some.inj (span.symm.trans indexed.columnSpan)
  subst indexChunk
  have indexFramed := indexed.frames
  rw [sameLimits] at indexFramed
  have sameFrames := Except.ok.inj (framed.symm.trans indexFramed)
  exact ⟨pages, sameFrames ▸ decoded, flatten⟩

public theorem read_plan_sound
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy}
    {decode : DecodePage α ε} {indexLimits : OffsetIndex.Limits}
    {group first stop : Nat} {result : Result α} {clips : List OffsetIndex.Window.Clip}
    (h : FlatColumn.Window.read binding limits policy decode indexLimits group first stop = .ok result)
    (planned : result.indexPlan = .ok (some clips)) :
    ∃ index selected column chunk bytes pages,
      OffsetIndex.Evidence { indexLimits with page := limits.framing } snapshot group binding.columnOrdinal
        index selected column chunk bytes ∧
      List.Forall₂ (CallbackWire decode binding.leaf column.metadata snapshot.bytes)
        (index.pages.map OffsetIndex.Entry.frame) pages ∧
      clips = OffsetIndex.Window.plan first stop index ∧
      result.rows = sliceRows first stop pages.flatten := by
  obtain ⟨slots, full, sliced, diagnostic⟩ := read_ok_iff.mp h
  obtain ⟨_, fullWire⟩ := readColumn_wire full
  rw [diagnostic] at planned
  obtain ⟨index, selected, column, chunk, bytes, evidence, clipsEq⟩ :=
    OffsetIndex.Window.planChecked_present planned
  obtain ⟨pages, allDecoded, slotsEq⟩ := sameColumnFrames fullWire evidence rfl
  exact ⟨index, selected, column, chunk, bytes, pages, evidence, allDecoded, clipsEq,
    sliced.trans (congrArg (sliceRows first stop) slotsEq)⟩

end Silmaril.Proofs.Formats.Parquet.FlatColumn.Window
