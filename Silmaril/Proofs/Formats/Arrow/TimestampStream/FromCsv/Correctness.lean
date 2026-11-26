module

public import Silmaril.Formats.Arrow.TimestampStream.FromCsv.Defs
import Silmaril.Formats.Relational.NamedTable.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.TimestampStream.FromCsv

open Silmaril.Relational Silmaril.Formats
open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.TimestampStream.FromCsv
open Silmaril.Formats.Arrow.TimestampStream.ToCsv (Cell CsvLimits Kind codecs schemaOf)
open Silmaril.Formats.Relational.NamedTable (Packed importCollected importCollected_ok_iff schemaMatches
  schemaMatches_eq_true_iff)

theorem checkSchema_sound {ipc : Limits} {declared : Csv.Typed.Schema Kind} {frame : KBytes}
    {binding : TimestampBatch.Binding} (checked : checkSchema ipc declared frame = .ok binding) :
    frame.wf = true ∧ TimestampStream.readSchema ipc frame = .ok (binding, frame.len) ∧
      schemaOf binding = declared := by
  by_cases wellFormed : frame.wf = true
  · cases opened : TimestampStream.readSchema ipc frame with
    | error reason => simp [checkSchema, wellFormed, opened, Except.mapError, Bind.bind, Except.bind] at checked
    | ok pair =>
      obtain ⟨actual, endOfSchema⟩ := pair
      by_cases complete : endOfSchema = frame.len
      · by_cases exactSchema : schemaMatches declared (schemaOf actual) = true
        · simp [checkSchema, wellFormed, opened, complete, exactSchema, Except.mapError, Bind.bind,
            Except.bind] at checked
          change Except.ok actual = .ok binding at checked
          cases checked
          exact ⟨wellFormed, by simp [complete], (schemaMatches_eq_true_iff _ _ |>.mp exactSchema).symm⟩
        · simp [checkSchema, wellFormed, opened, complete, exactSchema, Except.mapError, Bind.bind,
            Except.bind] at checked
      · simp [checkSchema, wellFormed, opened, complete, Except.mapError, Bind.bind, Except.bind] at checked
  · simp [checkSchema, wellFormed, Bind.bind, Except.bind] at checked

private theorem prepare_sound {ipc : Limits} {csv : CsvLimits} {declared : Csv.Typed.Schema Kind}
    {frame : KBytes} {wire : Csv.Bytes} {binding : TimestampBatch.Binding}
    {rows : Csv.Typed.Table (schemaOf binding) Cell}
    (prepared : prepare ipc csv declared frame wire = .ok ⟨binding, rows⟩) :
    checkSchema ipc declared frame = .ok binding ∧
      Csv.Typed.Utf8.decode (schemaOf binding) codecs wire = .ok rows ∧
      wire.length ≤ csv.maxBytes ∧ rows.length ≤ csv.maxRows := by
  by_cases bytesFit : csv.maxBytes < wire.length
  · simp [prepare, bytesFit, Bind.bind, Except.bind] at prepared
  · cases checked : checkSchema ipc declared frame with
    | error reason => simp [prepare, bytesFit, checked, Bind.bind, Except.bind] at prepared
    | ok actual =>
      cases decoded : Csv.Typed.Utf8.decode (schemaOf actual) codecs wire with
      | error reason => simp [prepare, bytesFit, checked, decoded, Except.mapError, Bind.bind, Except.bind] at prepared
      | ok table =>
        by_cases rowsFit : csv.maxRows < table.length
        · simp [prepare, bytesFit, checked, decoded, rowsFit, Except.mapError, Bind.bind, Except.bind] at prepared
        · have equal : (⟨actual, table⟩ :
              Σ b : TimestampBatch.Binding, Csv.Typed.Table (schemaOf b) Cell) = ⟨binding, rows⟩ :=
            Except.ok.inj (by
              simpa only [prepare, bytesFit, checked, decoded, rowsFit, ite_false, Except.mapError, Bind.bind,
                Except.bind, pure, Except.pure] using prepared)
          cases equal
          exact ⟨rfl, decoded, Nat.le_of_not_gt bytesFit, Nat.le_of_not_gt rowsFit⟩

private theorem certify_sound {ipc : Limits} {binding : TimestampBatch.Binding}
    {slots : TimestampBatch.Column binding} {wire : KBytes} (certified : certify ipc binding slots wire = .ok ()) :
    ∃ stream : TimestampStream.Stream,
      TimestampStream.read ipc wire = .ok stream ∧ schemaOf stream.binding = schemaOf binding ∧
      stream.batches.map tickCounts = [tickCounts slots] := by
  cases read : TimestampStream.read ipc wire with
  | error reason => simp [certify, read, Except.mapError, Bind.bind, Except.bind] at certified
  | ok stream =>
    have checked : (schemaMatches (schemaOf binding) (schemaOf stream.binding) &&
        decide (stream.batches.map tickCounts = [tickCounts slots])) = true := by
      by_cases agrees : (schemaMatches (schemaOf binding) (schemaOf stream.binding) &&
          decide (stream.batches.map tickCounts = [tickCounts slots])) = true
      · exact agrees
      · simp only [certify, read, Except.mapError, Bind.bind, Except.bind, agrees, ite_false,
          reduceCtorEq] at certified
    obtain ⟨sameSchema, sameRows⟩ := Bool.and_eq_true_iff.mp checked
    exact ⟨stream, rfl, (schemaMatches_eq_true_iff _ _ |>.mp sameSchema).symm, of_decide_eq_true sameRows⟩

theorem emit_readback {ipc : Limits} {binding : TimestampBatch.Binding} {frame wire : KBytes}
    {slots : TimestampBatch.Column binding} (emitted : emit ipc binding frame slots = .ok wire) :
    (∃ record, emitRecord ipc binding slots = .ok record ∧ wire = frame ++ record ++ StreamWriter.eos) ∧
    ∃ stream : TimestampStream.Stream,
      TimestampStream.read ipc wire = .ok stream ∧ schemaOf stream.binding = schemaOf binding ∧
      stream.batches.map tickCounts = [tickCounts slots] := by
  cases record : emitRecord ipc binding slots with
  | error reason => simp [emit, record, Bind.bind, Except.bind] at emitted
  | ok batch =>
    let complete := frame ++ batch ++ StreamWriter.eos
    cases checked : certify ipc binding slots complete with
    | error reason =>
      simp [emit, record, show certify ipc binding slots (frame ++ batch ++ StreamWriter.eos) = .error reason
        from checked, Bind.bind, Except.bind] at emitted
    | ok done =>
      cases done
      have exactWire : complete = wire := Except.ok.inj (by
        simpa only [emit, record, show certify ipc binding slots (frame ++ batch ++ StreamWriter.eos) = .ok ()
          from checked, Bind.bind, Except.bind, pure, Except.pure] using emitted)
      rw [← exactWire]
      exact ⟨⟨batch, rfl, rfl⟩, certify_sound checked⟩

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {ipc : Limits} {csv : CsvLimits}
variable {declared : Csv.Typed.Schema Kind} {frame : KBytes} {wire : Csv.Bytes}

theorem convert_readback {result : Result Name}
    (converted : convert db name ipc csv declared frame wire = .ok result) :
    db name = none ∧ ∃ (binding : TimestampBatch.Binding)
      (rows : Csv.Typed.Table (schemaOf binding) Cell) (stream : TimestampStream.Stream),
      frame.wf = true ∧ TimestampStream.readSchema ipc frame = .ok (binding, frame.len) ∧
      schemaOf binding = declared ∧ Csv.Typed.Utf8.decode (schemaOf binding) codecs wire = .ok rows ∧
      wire.length ≤ csv.maxBytes ∧ rows.length ≤ csv.maxRows ∧
      result.db = Function.update db name (some ⟨schemaOf binding, rows⟩) ∧
      TimestampStream.read ipc result.wire = .ok stream ∧ schemaOf stream.binding = declared ∧
      stream.batches.map tickCounts = [tickCounts (slotsOf binding rows)] := by
  cases occupied : db name with
  | some prior => simp [convert, occupied] at converted
  | none =>
    simp only [convert, occupied, Option.isSome_none, Bool.false_eq_true, ite_false] at converted
    cases prepared : prepare ipc csv declared frame wire with
    | error reason => simp [prepared] at converted
    | ok table =>
      obtain ⟨binding, rows⟩ := table
      cases written : emit ipc binding frame (slotsOf binding rows) with
      | error reason => simp [prepared, written] at converted
      | ok output =>
        have inserted : importCollected (Error := Csv.Typed.Error) db name (schemaOf binding)
            (.ok ⟨⟨schemaOf binding, rows⟩, .eos⟩) =
            .ok (Function.update db name (some ⟨schemaOf binding, rows⟩)) :=
          (importCollected_ok_iff _ _ _ _ _).mpr ⟨occupied, rows, rfl, rfl⟩
        simp only [prepared, written, inserted, Except.ok.injEq] at converted
        subst result
        obtain ⟨checked, decoded, bytesFit, rowsFit⟩ := prepare_sound prepared
        obtain ⟨wellFormed, exactFrame, sameSchema⟩ := checkSchema_sound checked
        obtain ⟨_, stream, read, descriptor, counts⟩ := emit_readback written
        exact ⟨rfl, binding, rows, stream, wellFormed, exactFrame, sameSchema, decoded, bytesFit, rowsFit,
          rfl, read, descriptor.trans sameSchema, counts⟩

end Silmaril.Proofs.Formats.Arrow.TimestampStream.FromCsv
