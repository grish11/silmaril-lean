module

public import Silmaril.Formats.Arrow.DateStream.ToCsv.RowObservational.Defs
import Silmaril.Formats.Arrow.DateStream.FromCsv.Thms
import Silmaril.Formats.Arrow.DateStream.ToCsv.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Date32.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.DateStream.ToCsv.RowObservational

open Silmaril.Formats Arrow DateStream.ToCsv DateStream.ToCsv.RowObservational

private theorem slots_rows (name : String) (nullable : Bool) (slots : DateStream.Writer.Column) :
    DateStream.FromCsv.slots (rows name nullable slots) = slots := by
  simp [DateStream.FromCsv.slots, rows, List.map_map, Function.comp_def]

theorem readRows_eq_ok_iff {ipc : Limits} {name : String} {nullable : Bool}
    {input : KBytes} {slots : DateStream.Writer.Column} :
    readRows ipc name nullable input = .ok slots ↔
      ∃ source, DateStream.read ipc input = .ok source ∧ source.field = ⟨name, nullable, .day⟩ ∧
        slots.map (Option.map DateInterop.Date32.toCivil) = source.batches.flatten := by
  unfold DateStream.ToCsv.RowObservational.readRows
  cases DateStream.read ipc input with
  | error cause => simp [Except.mapError, Bind.bind, Except.bind]
  | ok source =>
    by_cases field : source.field = ⟨name, nullable, .day⟩
    · simp only [Except.mapError, Bind.bind, Except.bind, field, ne_eq, not_true_eq_false, ite_false,
        Except.ok.injEq, exists_eq_left', true_and]
      rw [← Internal.recover_eq_some_iff]
      cases Internal.recover source.batches.flatten
      · simp
      · simp [Pure.pure, Except.pure]
    · simp [Except.mapError, Bind.bind, Except.bind, field, MonadExcept.throw]

theorem exportRows_eq_ok_iff {ipc : Limits} {csv : DateStream.FromCsv.CsvLimits}
    {name : String} {nullable : Bool} {input : KBytes} {wire : Csv.Bytes} :
    exportRows ipc csv name nullable input = .ok wire ↔
      wire.length ≤ csv.maxBytes ∧
      ∃ slots, readRows ipc name nullable input = .ok slots ∧ slots.length ≤ csv.maxRows ∧
        Csv.Typed.Codecs.Date32.encode (DateStream.FromCsv.schema name nullable) id
          (rows name nullable slots) = .ok wire := by
  unfold exportRows
  cases readRows ipc name nullable input <;>
    simp [Except.bind, Bind.bind, Internal.encodeColumn_eq_ok_iff]

theorem exportRows_eq_iff {ipc : Limits} {csv : DateStream.FromCsv.CsvLimits}
    {name : String} {nullable : Bool} {left right : KBytes} {leftWire rightWire : Csv.Bytes}
    (wroteLeft : exportRows ipc csv name nullable left = .ok leftWire)
    (wroteRight : exportRows ipc csv name nullable right = .ok rightWire) :
    leftWire = rightWire ↔ readRows ipc name nullable left = readRows ipc name nullable right := by
  obtain ⟨_, leftSlots, readLeft, _, encodedLeft⟩ := exportRows_eq_ok_iff.mp wroteLeft
  obtain ⟨_, rightSlots, readRight, _, encodedRight⟩ := exportRows_eq_ok_iff.mp wroteRight
  rw [readLeft, readRight, Except.ok.injEq]
  constructor
  · rintro rfl
    have same := (Csv.Typed.Codecs.Date32.decode_encode encodedLeft).symm.trans
      (Csv.Typed.Codecs.Date32.decode_encode encodedRight)
    have equal := congrArg (DateStream.FromCsv.slots (name := name) (nullable := nullable))
      (Except.ok.inj same)
    rwa [slots_rows, slots_rows] at equal
  · rintro rfl
    exact Except.ok.inj (encodedLeft.symm.trans encodedRight)

theorem reimport_readback {ipc : Limits} {reimport : ObservationLimits}
    {csv : DateStream.FromCsv.CsvLimits} {name : String} {nullable : Bool}
    {input output : KBytes} {wire : Csv.Bytes}
    (exported : exportRows ipc csv name nullable input = .ok wire)
    (imported : DateStream.FromCsv.convert reimport csv name nullable wire = .ok output) :
    ∃ slots, readRows ipc name nullable input = .ok slots ∧
      DateStream.read reimport.ipc output = .ok (DateStream.Writer.observation name nullable [slots]) := by
  obtain ⟨_, slots, source, _, encoded⟩ := exportRows_eq_ok_iff.mp exported
  obtain ⟨table, stream, parsed, readback, same, _⟩ := DateStream.FromCsv.convert_readback imported
  have tableEq := Except.ok.inj (parsed.symm.trans (Csv.Typed.Codecs.Date32.decode_encode encoded))
  subst table
  exact ⟨slots, source, by rwa [same, slots_rows] at readback⟩

end Silmaril.Proofs.Formats.Arrow.DateStream.ToCsv.RowObservational
