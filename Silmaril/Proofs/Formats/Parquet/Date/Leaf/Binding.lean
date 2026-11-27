module

public import Silmaril.Formats.Parquet.Date.Leaf.Defs
import all Silmaril.Formats.Parquet.Date.Leaf.Defs
import Silmaril.Formats.Parquet.Footer.ColumnOrder.Thms
import Silmaril.Formats.Parquet.FlatScan.Thms
import all Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
public import Batteries.Data.List.Basic

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf

open Silmaril.Formats Parquet Date.Leaf

theorem bind_exact {limits : Footer.Limits} {snapshot : Snapshot.Checked} {ordinal : Nat}
    {bound : Bound} (accepted : bind limits snapshot ordinal = .ok bound) :
    bound.snapshot = snapshot ∧ bound.ordinal = ordinal ∧ Date.IsDateLeaf bound.binding.leaf ∧
      ∃ selected, Footer.ColumnOrder.FlatWire limits snapshot ordinal selected ∧
        selected.leaf = bound.binding.leaf ∧
        Date.Internal.readAnnotation selected.selection.reader selected.selection.leaf.item.fields =
          .ok bound.binding.annotation := by
  cases flat : Footer.ColumnOrder.readFlat limits snapshot ordinal with
  | error cause =>
    simp [Date.Leaf.bind, Internal.bindSelection, flat, Except.map, Except.mapError, Bind.bind, Except.bind] at accepted
  | ok selected =>
    by_cases date : Date.IsDateLeaf selected.leaf
    · cases annotation : Date.Internal.readAnnotation selected.selection.reader
          selected.selection.leaf.item.fields with
      | error cause =>
        simp [Date.Leaf.bind, Internal.bindSelection, flat, date, annotation, Except.map, Except.mapError,
          Bind.bind, Except.bind] at accepted
      | ok annotationKind =>
        simp [Date.Leaf.bind, Internal.bindSelection, flat, date, annotation, Except.map, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted
        subst bound
        exact ⟨rfl, rfl, date, selected, Footer.ColumnOrder.readFlat_wire flat, rfl, annotation⟩
    · simp [Date.Leaf.bind, Internal.bindSelection, flat, date, Except.map, Except.mapError, Bind.bind,
        Except.bind, MonadExcept.throw] at accepted

theorem open_exact {limits : Snapshot.Limits} {source : Bytes} {ordinal : Nat} {bound : Bound}
    (opened : openLeaf limits source ordinal = .ok bound) :
    Snapshot.check (Failure := Unit) limits source = .ok bound.snapshot ∧
      bind limits.footer bound.snapshot ordinal = .ok bound := by
  cases checked : Snapshot.check (Failure := Unit) limits source with
  | error cause => simp [openLeaf, checked, Except.mapError, Bind.bind, Except.bind] at opened
  | ok snapshot =>
    have bound := show bind limits.footer snapshot ordinal = .ok bound by
      simpa [openLeaf, checked, Except.mapError, Bind.bind, Except.bind] using opened
    have same := (bind_exact bound).1
    exact ⟨by rw [same], by rwa [same]⟩

theorem selectChunk_exact {bound : Bound} {index : Nat} {chunk : Chunk}
    (selected : selectChunk bound index = .ok chunk) :
    bound.snapshot.groupAt index = some chunk.group ∧
      chunk.group.columns[bound.ordinal]? = some chunk.column ∧
      chunk.column.metadata.pathInSchema = [bound.binding.leaf.name] ∧
      chunk.column.metadata.physicalType = .int32 ∧
      Page.columnSpan bound.snapshot.footer.start chunk.column.metadata = some chunk.span ∧
      Internal.disjoint bound.snapshot index bound.ordinal chunk.span = true := by
  cases grouped : bound.snapshot.groupAt index with
  | none => simp [selectChunk, grouped, MonadExcept.throw] at selected
  | some group =>
    cases columnAt : group.columns[bound.ordinal]? with
    | none => simp [selectChunk, grouped, columnAt, MonadExcept.throw] at selected
    | some column =>
      by_cases associated : column.metadata.pathInSchema = [bound.binding.leaf.name] ∧
          column.metadata.physicalType = .int32
      · obtain ⟨path, physical⟩ := associated
        cases extent : Page.columnSpan bound.snapshot.footer.start column.metadata with
        | none =>
          simp [selectChunk, grouped, columnAt, path, physical, extent, MonadExcept.throw] at selected
        | some span =>
          by_cases separated : Internal.disjoint bound.snapshot index bound.ordinal span = true
          · simp [selectChunk, grouped, columnAt, path, physical, extent, separated,
              Pure.pure, Except.pure] at selected
            subst chunk
            exact ⟨rfl, columnAt, path, physical, extent, separated⟩
          · simp [selectChunk, grouped, columnAt, path, physical, extent, separated,
              MonadExcept.throw, Bind.bind, Except.bind] at selected
      · have wrong : column.metadata.pathInSchema ≠ [bound.binding.leaf.name] ∨
            column.metadata.physicalType ≠ .int32 := by rwa [not_and_or] at associated
        simp [selectChunk, grouped, columnAt, wrong, MonadExcept.throw, Bind.bind, Except.bind]
          at selected

theorem readGroup_exact {limits : Date.Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ chunk frames pages, selectChunk bound index = .ok chunk ∧
      Page.readChunk limits.scan.page bound.snapshot.bytes chunk.span = .ok frames ∧
      Page.Chain chunk.span chunk.span.start chunk.span.stop frames ∧
      List.Forall₂ (PageWire limits.page bound) frames pages ∧
      slots = pages.flatten ∧ slots.length = chunk.group.numRows.toNat := by
  cases selected : selectChunk bound index with
  | error cause => simp [readGroup, selected, Bind.bind, Except.bind] at read
  | ok chunk =>
    cases scanned : FlatScan.scanColumn limits.scan (FlatScan.decodeInt32Page limits.page)
        bound.snapshot.bytes bound.snapshot.footer.start bound.field chunk.group.numRows.toNat
        chunk.column with
    | error cause =>
      simp [readGroup, selected, scanned, Except.mapError, Bind.bind, Except.bind] at read
    | ok values =>
      have same : values.cells.toList = slots := by
        simpa [readGroup, selected, scanned, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure] using read
      obtain ⟨span, frames, pages, spanAt, framed, decoded, concatenated⟩ :=
        FlatScan.scanColumn_wire scanned
      have expected := (selectChunk_exact selected).2.2.2.2.1
      have exactRange : span = chunk.span := Option.some.inj (spanAt.symm.trans expected)
      subst span
      exact ⟨chunk, frames, pages, rfl, framed, (Page.readChunk_chain framed).2.2, decoded,
        same.symm.trans concatenated, by simpa [← same] using values.sized⟩

theorem pageWire_exact {limits : ScalarPage.Limits} {bound : Bound} {frame : Page.Frame}
    {slots : Slots} (decoded : PageWire limits bound frame slots) :
    let body := Footer.fileBytes bound.snapshot.bytes frame.payload.start frame.payload.stop
    ∃ params layout prepared words, FlatScan.int32PageParameters bound.field frame.value = some params ∧
      ScalarPage.validate params limits body = .ok layout ∧
      ScalarPage.PreparedWire params limits layout body prepared ∧
      ScalarPage.Kind.int32.readPlain (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words := by
  let body := Footer.fileBytes bound.snapshot.bytes frame.payload.start frame.payload.stop
  have raw := decoded.2
  cases parameters : FlatScan.int32PageParameters bound.field frame.value with
  | none =>
    simp [FlatScan.decodeInt32Page, parameters] at raw
  | some params =>
    have read : ScalarPage.decode .int32 params limits body = .ok slots := by
      cases outcome : ScalarPage.decode .int32 params limits body <;>
        simp [FlatScan.decodeInt32Page, parameters, body, outcome, Except.mapError] at raw ⊢
      exact raw
    obtain ⟨prepared, words, preparation, plain, mask, ordered, _, _⟩ := ScalarPage.decode_sound read
    obtain ⟨layout, valid, exactBody⟩ := ScalarPage.prepare_sound preparation
    exact ⟨params, layout, prepared, words, rfl, valid, exactBody, plain, mask, ordered⟩

end Silmaril.Proofs.Formats.Parquet.Date.Leaf
