module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Defs
import Silmaril.Formats.Parquet.Footer.Thms
import Silmaril.Formats.Parquet.PlainV1Writer.Thms
public import Batteries.Data.List.Basic
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatInt32Writer

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatInt32Writer

private theorem emitChunks_sound {limits : PlainV1Writer.Limits} {start : Nat}
    {columns : List Column} {chunks : List Chunk} (written : emitChunks limits start columns = .ok chunks) :
    List.Forall₂ (fun column chunk => chunk.column = column ∧
      PlainV1Writer.emit limits column.values = .ok chunk.page) columns chunks ∧
    Contiguous start chunks (start + (chunks.map (fun chunk => chunk.page.wire.length)).sum) := by
  induction columns generalizing start chunks with
  | nil =>
    simp only [emitChunks, Except.ok.injEq] at written
    subst chunks
    exact ⟨.nil, by simp [Contiguous]⟩
  | cons column columns ih =>
    cases emitted : PlainV1Writer.emit limits column.values with
    | error error => simp [emitChunks, emitted, Except.mapError, Bind.bind, Except.bind] at written
    | ok page =>
      let first : Chunk := ⟨column, page, start⟩
      cases next : emitChunks limits first.stop columns with
      | error error =>
        simp [emitChunks, emitted, Except.mapError, Bind.bind, Except.bind, first, next] at written
      | ok rest =>
        simp [emitChunks, emitted, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
          first, next] at written
        subst chunks
        obtain ⟨related, contiguous⟩ := ih next
        refine ⟨.cons ⟨rfl, emitted⟩ related, rfl, ?_⟩
        simpa [first, Chunk.stop, Nat.add_assoc] using contiguous

private theorem assemble_sound {limits : Limits} {input : Input} {output : Encoded}
    (built : assemble limits input = .ok output) :
    emitChunks limits.page 4 input.columns = .ok output.chunks ∧
      output.metadata = Compact.metadata input.rowCount (output.chunks.map Chunk.index) := by
  cases measured : input.columns.mapM (fun col => measuredPage limits.page col.values) with
  | error error => simp [assemble, measured, Bind.bind, Except.bind] at built
  | ok sizes =>
    let fileLimit := min limits.maxFileBytes (2 ^ 63 - 1)
    let footerStart := 4 + sizes.sum
    by_cases bound : fileLimit < footerStart + 8
    · simp [assemble, measured, fileLimit, footerStart, bound, Bind.bind, Except.bind] at built
    · cases paged : emitChunks limits.page 4 input.columns with
      | error error =>
        simp [assemble, measured, fileLimit, footerStart, bound, paged, Bind.bind, Except.bind] at built
      | ok chunks =>
        let cap := min (min limits.footer.maxFooterBytes (2 ^ 32 - 1)) (fileLimit - footerStart - 8)
        cases footer : Compact.encode cap input.rowCount (chunks.map Chunk.index) with
        | error error =>
          simp [cap, fileLimit, footerStart] at footer
          simp [assemble, measured, fileLimit, footerStart, bound, paged, footer,
            Except.mapError, Bind.bind, Except.bind] at built
        | ok metadataBytes =>
          simp [cap, fileLimit, footerStart] at footer
          simp [assemble, measured, fileLimit, footerStart, bound, paged, footer,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
          subst output
          exact ⟨rfl, rfl⟩

private theorem emit_parts {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    input.Valid limits ∧ output.Checked limits input.rowCount ∧ assemble limits input = .ok output := by
  by_cases valid : input.Valid limits
  · cases built : assemble limits input with
    | error error => simp [emit, valid, built, Bind.bind, Except.bind] at written
    | ok candidate =>
      by_cases checked : candidate.Checked limits input.rowCount
      · simp [emit, valid, built, checked, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
        subst output
        exact ⟨valid, checked, rfl⟩
      · simp [emit, valid, built, checked, Bind.bind, Except.bind] at written
  · simp [emit, valid] at written

theorem emit_layout {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    input.Valid limits ∧ output.Checked limits input.rowCount ∧
      output.metadata = Compact.metadata input.rowCount (output.chunks.map Chunk.index) ∧
      Contiguous 4 output.chunks output.footer.start ∧
      Footer.Framed limits.footer.maxFooterBytes output.bytes output.footer := by
  obtain ⟨valid, checked, built⟩ := emit_parts written
  obtain ⟨paged, metadata⟩ := assemble_sound built
  obtain ⟨_, contiguous⟩ := emitChunks_sound paged
  refine ⟨valid, checked, metadata, ?_, (Footer.readFooter_ok_iff.mp checked.2.2.2.1).1⟩
  rw [checked.2.2.1]
  exact contiguous

theorem emit_columns {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    List.Forall₂ (fun column chunk => chunk.column = column ∧
      chunk.Checked limits output.bytes output.footer.start input.rowCount ∧
      chunk.frame.value = column.values.header ∧ column.values.Fits limits.page ∧
      ScalarPage.decode .int32 column.values.parameters limits.page.scalar
        (Footer.fileBytes output.bytes chunk.frame.payload.start chunk.frame.payload.stop) =
        .ok column.values.slots) input.columns output.chunks := by
  obtain ⟨_, checked, built⟩ := emit_parts written
  obtain ⟨paged, _⟩ := assemble_sound built
  obtain ⟨paired, _⟩ := emitChunks_sound paged
  have checkAll := checked.2.2.2.2.2
  clear written checked built paged
  generalize input.columns = columns at paired ⊢
  generalize output.chunks = chunks at paired checkAll ⊢
  induction paired with
  | nil => exact .nil
  | cons pair _ ih =>
    have first := checkAll _ (List.mem_cons_self)
    obtain ⟨bounded, _, header, _⟩ := PlainV1Writer.emit_exact pair.2
    refine .cons ⟨pair.1, first, header, bounded, ?_⟩
      (ih (fun chunk member => checkAll chunk (List.mem_cons_of_mem _ member)))
    rw [first.2.2]
    exact PlainV1Writer.emit_roundTrip pair.2

end Silmaril.Proofs.Formats.Parquet.FlatInt32Writer
