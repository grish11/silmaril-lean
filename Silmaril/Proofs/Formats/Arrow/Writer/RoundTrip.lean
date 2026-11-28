module

public import Silmaril.Formats.Arrow.Writer.Defs
import Silmaril.Formats.Arrow.Body.Thms
import Silmaril.Formats.Arrow.Layout.Thms
import Silmaril.Proofs.Formats.Arrow.Writer.Assembly
import Silmaril.Proofs.Formats.Arrow.Writer.Buffers
import Silmaril.Proofs.Formats.Arrow.Writer.Columns
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.Writer

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.Writer

theorem checkInput_iff (limits : ObservationLimits) (input : BatchInput) :
    checkInput limits input = .ok () ↔ Admitted limits input := by
  constructor
  · intro accepted
    by_cases fields : input.columns.length ≤ limits.ipc.fields
    · by_cases rows : input.rowCount ≤ limits.ipc.rows
      · cases budget : Body.checkBudget limits input.columns.length input.rowCount with
        | error reason =>
          simp [checkInput, Nat.not_lt.mpr fields, Nat.not_lt.mpr rows, budget,
            Bind.bind, Except.bind] at accepted
        | ok done =>
          cases done
          by_cases shape : input.Shape
          · by_cases offsets : input.OffsetsFit
            · by_cases bytes : input.bodySize ≤ limits.ipc.bodyBytes
              · by_cases wire : input.WireSize
                · exact ⟨fields, rows, budget, shape, offsets, bytes, wire⟩
                · simp [checkInput, Nat.not_lt.mpr fields, Nat.not_lt.mpr rows, budget,
                    shape, offsets, bytes, wire, Bind.bind, Except.bind] at accepted
              · simp [checkInput, Nat.not_lt.mpr fields, Nat.not_lt.mpr rows, budget,
                  shape, offsets, bytes, Bind.bind, Except.bind] at accepted
            · simp [checkInput, Nat.not_lt.mpr fields, Nat.not_lt.mpr rows, budget,
                shape, offsets, Bind.bind, Except.bind] at accepted
          · simp [checkInput, Nat.not_lt.mpr fields, Nat.not_lt.mpr rows, budget,
              shape, Bind.bind, Except.bind] at accepted
      · have over : limits.ipc.rows < input.rowCount := by omega
        simp [checkInput, Nat.not_lt.mpr fields, over, Bind.bind, Except.bind] at accepted
    · have over : limits.ipc.fields < input.columns.length := by omega
      simp [checkInput, over, Bind.bind, Except.bind] at accepted
  · rintro ⟨fields, rows, budget, shape, offsets, bytes, wire⟩
    simp [checkInput, Nat.not_lt.mpr fields, Nat.not_lt.mpr rows, budget, shape, offsets,
      bytes, wire, Bind.bind, Except.bind, pure, Except.pure]

private theorem partsCount (columns : List NamedColumn) :
    (columns.flatMap fun c => c.values.emit).length =
      (columns.map fun c => c.field.type.bufferCount).sum := by
  induction columns with
  | nil => rfl
  | cons column columns ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    rw [ih]
    rcases column with ⟨name, nullable, values⟩
    cases values <;> rfl

private theorem pieceSizes (columns : List NamedColumn) :
    ((columns.flatMap fun column => column.values.emit).map KBytes.len) =
      columns.flatMap (fun column => column.values.bufferSizes) := by
  induction columns with
  | nil => rfl
  | cons column columns ih =>
    simp only [List.flatMap_cons, List.map_append, emit_sizes, ih]

private theorem packedSize (input : BatchInput) :
    (packBuffers 0 (input.columns.flatMap fun c => c.values.emit)).2.len = input.bodySize := by
  rw [packBuffers_length]
  unfold BatchInput.bodySize
  congr 1
  change (List.map ((fun size => size + padding size) ∘ KBytes.len) _) = _
  rw [← List.map_map, pieceSizes]

private theorem zippedShape (columns : List NamedColumn) (rowCount : Nat)
    (fits : ∀ c ∈ columns, c.node.Fits rowCount c.field) :
    ∀ pair ∈ (columns.map NamedColumn.field).zip (columns.map NamedColumn.node),
      pair.2.Fits rowCount pair.1 := by
  induction columns with
  | nil => simp
  | cons column columns ih =>
    intro pair member
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact fits column (by simp)
    · exact ih (fun c h => fits c (List.mem_cons_of_mem _ h)) pair member

theorem emitBatch_of_admitted (limits : ObservationLimits) (input : BatchInput)
    (allowed : Admitted limits input) :
    ∃ frame, emitBatch limits input = .ok frame ∧
      frame.metadata.rowCount = input.rowCount ∧ frame.body.len % 8 = 0 ∧
      decodeBatch limits frame = .ok input.observe := by
  let pieces := input.columns.flatMap fun c => c.values.emit
  let packed := packBuffers 0 pieces
  have piecesWF : ∀ part ∈ pieces, part.wf = true := by
    intro part member
    obtain ⟨column, _, h⟩ := List.mem_flatMap.mp member
    exact emit_wf column.values part h
  have wf : packed.2.wf = true := packBuffers_wf 0 pieces piecesWF
  have bufferFit : BuffersFit packed.2.len 0 packed.1 := by
    simpa only [Nat.zero_add] using packBuffers_fits 0 pieces rfl
  let metadata : RecordBatch := ⟨input.rowCount, input.columns.map NamedColumn.node, packed.1⟩
  have fits : metadata.Fits input.fields packed.2.len := by
    refine ⟨by simp [metadata, BatchInput.fields], ?_, zippedShape _ _ allowed.shape, bufferFit⟩
    change packed.1.length = (input.fields.map fun f => f.type.bufferCount).sum
    rw [packBuffers_count]
    simpa only [BatchInput.fields, List.map_map, Function.comp_def] using partsCount input.columns
  let frame : BatchFrame input.fields := ⟨metadata, packed.2, fits⟩
  have checked : validateBatch input.fields metadata packed.2 = .ok frame := by
    simp [validateBatch, fits, frame]
  have budget : Body.checkBatch limits frame = .ok () := by
    have bytes : frame.body.len ≤ limits.ipc.bodyBytes := by
      change (packBuffers 0 pieces).2.len ≤ limits.ipc.bodyBytes
      exact packedSize input ▸ allowed.bodyBytes
    simp [Body.checkBatch, frame, metadata, BatchInput.fields, wf, Nat.not_lt.mpr allowed.fields,
      Nat.not_lt.mpr allowed.rows, Nat.not_lt.mpr bytes, allowed.budget]
  refine ⟨frame, ?_, rfl, packBuffers_aligned 0 pieces, ?_⟩
  · simp only [emitBatch, (checkInput_iff limits input).mpr allowed, Bind.bind, Except.bind]
    exact checked
  apply (Silmaril.Formats.Arrow.decodeBatch_iff limits frame input.observe).mpr
  refine ⟨budget, input.columns.map (fun c => c.values.observe), ?_, rfl⟩
  exact packedColumns packed.2 0 input.columns packed.1 wf
    (fun b member => (BuffersFit.mem_fits bufferFit member).2.2) allowed.offsets
    (by simpa using packBuffers_exact [] pieces piecesWF)

theorem emitBatch_roundtrip {limits : ObservationLimits} {input : BatchInput}
    {frame : BatchFrame input.fields} (written : emitBatch limits input = .ok frame) :
    frame.metadata.rowCount = input.rowCount ∧ frame.body.len % 8 = 0 ∧
      decodeBatch limits frame = .ok input.observe := by
  cases inputCheck : checkInput limits input with
  | error reason => simp [emitBatch, inputCheck, Bind.bind, Except.bind] at written
  | ok done =>
    cases done
    obtain ⟨expected, eq, count, aligned, read⟩ :=
      emitBatch_of_admitted limits input ((checkInput_iff limits input).mp inputCheck)
    obtain rfl := Except.ok.inj (written.symm.trans eq)
    exact ⟨count, aligned, read⟩

end Silmaril.Proofs.Formats.Arrow.Writer
