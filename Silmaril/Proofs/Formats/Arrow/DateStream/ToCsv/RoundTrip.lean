module

public import Silmaril.Formats.Arrow.DateStream.ToCsv.Defs
public import Silmaril.Formats.Arrow.DateStream.FromCsv.Thms
public import Silmaril.Formats.Arrow.DateStream.Writer.Thms
public import Silmaril.Formats.Csv.Typed.Codecs.Date32.Thms
public import Silmaril.Formats.DateInterop.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.DateStream.ToCsv

open Silmaril.Formats Arrow DateStream.ToCsv
open Silmaril.Numeric.Gregorian (CivilDate)
open Silmaril.Formats.DateInterop

private theorem recoverSlot {date : Option CivilDate} {word : Option Date32.Payload} :
    date.mapM Date32.ofCivil? = some word ↔ word.map Date32.toCivil = date := by
  cases date <;> cases word <;> simp [Option.mapM, Date32.ofCivil?_eq_some_iff]

private theorem cons_some_iff {α : Type*} (head : Option α) (tail : Option (List α))
    (output : List α) :
    (do let a ← head; let as ← tail; pure (a :: as)) = some output ↔
      ∃ a as, head = some a ∧ tail = some as ∧ a :: as = output := by
  cases head <;> cases tail <;> simp

private theorem recoverColumn (dates : DateValues.Column) (slots : DateStream.Writer.Column) :
    dates.mapM (fun d => d.mapM Date32.ofCivil?) = some slots ↔
      slots.map (Option.map Date32.toCivil) = dates := by
  induction dates generalizing slots with
  | nil => cases slots <;> simp
  | cons date tail ih =>
    rw [List.mapM_cons, cons_some_iff]
    cases slots with
    | nil => simp
    | cons first rest => simp [recoverSlot, ih]

private theorem rows_slots {name : String} {nullable : Bool}
    (table : Csv.Typed.Table (DateStream.FromCsv.schema name nullable) Csv.Typed.Codecs.Date32.Cell) :
    rows name nullable (DateStream.FromCsv.slots table) = table := by
  induction table with
  | nil => rfl
  | cons row tail ih =>
    simp only [DateStream.FromCsv.slots, rows, List.map_cons, List.map_map] at ih ⊢
    congr 1
    funext i
    have same : i = ⟨0, Nat.zero_lt_succ 0⟩ := by
      apply Fin.ext
      change i.val = 0
      have bound : i.val < 1 := i.isLt
      exact Nat.lt_one_iff.mp bound
    rw [same]

theorem readColumn_eq_ok_iff {ipc : Limits} {name : String} {nullable : Bool}
    {input : KBytes} {slots : DateStream.Writer.Column} :
    readColumn ipc name nullable input = .ok slots ↔
      DateStream.read ipc input = .ok (DateStream.Writer.observation name nullable [slots]) := by
  cases sourceRead : DateStream.read ipc input with
  | error cause => simp [readColumn, sourceRead, Except.mapError, Bind.bind, Except.bind]
  | ok source =>
    rcases source with ⟨field, batches⟩
    by_cases descriptor : field = ⟨name, nullable, .day⟩
    · subst field
      cases batches with
      | nil =>
        simp [readColumn, sourceRead, Except.mapError, Bind.bind, Except.bind,
          DateStream.Writer.observation]
      | cons dates tail =>
        cases tail with
        | nil =>
          simp only [readColumn, sourceRead, Except.mapError, Bind.bind, Except.bind,
            ne_eq, not_true_eq_false, ite_false, DateStream.Writer.observation, List.map_cons,
            List.map_nil, Except.ok.injEq, DateStream.Stream.mk.injEq, true_and, List.cons.injEq]
          have exactSlots := recoverColumn dates slots
          cases recovered : dates.mapM (fun d => d.mapM Date32.ofCivil?) <;>
            rw [recovered] at exactSlots <;>
            simpa [Pure.pure, Except.pure, eq_comm] using exactSlots
        | cons next more =>
          simp [readColumn, sourceRead, Except.mapError, Bind.bind, Except.bind,
            DateStream.Writer.observation]
    · simp [readColumn, sourceRead, Except.mapError, Bind.bind, Except.bind, descriptor,
        DateStream.Writer.observation, MonadExcept.throw]

theorem convert_eq_ok_iff {ipc : Limits} {csv : DateStream.FromCsv.CsvLimits} {name : String}
    {nullable : Bool} {input : KBytes} {output : Csv.Bytes} :
    convert ipc csv name nullable input = .ok output ↔
      output.length ≤ csv.maxBytes ∧
      ∃ slots, DateStream.read ipc input = .ok (DateStream.Writer.observation name nullable [slots]) ∧
        slots.length ≤ csv.maxRows ∧
        Csv.Typed.Codecs.Date32.encode (DateStream.FromCsv.schema name nullable) id
          (rows name nullable slots) = .ok output := by
  simp only [← readColumn_eq_ok_iff]
  unfold convert
  cases readColumn ipc name nullable input with
  | error cause => simp [Bind.bind, Except.bind]
  | ok slots =>
    by_cases count : slots.length ≤ csv.maxRows
    · simp only [count, not_lt.mpr count, ite_false, Bind.bind, Except.bind, Except.ok.injEq,
        exists_eq_left', true_and]
      cases Csv.Typed.Codecs.Date32.encode (DateStream.FromCsv.schema name nullable) id
          (rows name nullable slots) with
      | error cause => simp [Except.mapError]
      | ok encoded =>
        by_cases same : encoded = output
        · subst output
          by_cases size : encoded.length ≤ csv.maxBytes
          · simp [Except.mapError, not_lt.mpr size, size, Pure.pure, Except.pure]
          · simp [Except.mapError, Nat.lt_of_not_ge size, size, MonadExcept.throw]
        · by_cases size : encoded.length ≤ csv.maxBytes
          · simp [Except.mapError, not_lt.mpr size, same, Pure.pure, Except.pure]
          · simp [Except.mapError, Nat.lt_of_not_ge size, same, MonadExcept.throw]
    · simp [Bind.bind, Except.bind, Nat.lt_of_not_ge count, count, MonadExcept.throw]

theorem csv_roundtrip {ipc : ObservationLimits} {csv : DateStream.FromCsv.CsvLimits} {name : String}
    {nullable : Bool} {input : Csv.Bytes} {wire : KBytes}
    (written : DateStream.FromCsv.convert ipc csv name nullable input = .ok wire) :
    ∃ table canonical,
      Csv.Typed.Codecs.Date32.decode (DateStream.FromCsv.schema name nullable) id input = .ok table ∧
      Csv.Typed.Codecs.Date32.encode (DateStream.FromCsv.schema name nullable) id table = .ok canonical ∧
      Csv.Utf8.decode canonical = Csv.Utf8.decode input ∧
      (convert ipc.ipc csv name nullable wire = .ok canonical ↔ canonical.length ≤ csv.maxBytes) := by
  obtain ⟨_, table, decoded, bounded, emitted⟩ := DateStream.FromCsv.convert_eq_ok_iff.mp written
  obtain ⟨canonical, encoded, same⟩ := Csv.Typed.Codecs.Date32.encode_of_decode decoded
  refine ⟨table, canonical, decoded, encoded, same, fun exported => (convert_eq_ok_iff.mp exported).1, fun size => ?_⟩
  refine convert_eq_ok_iff.mpr ⟨size, DateStream.FromCsv.slots table,
    DateStream.Writer.emit_readback emitted, ?_, ?_⟩
  · simpa [DateStream.FromCsv.slots] using bounded
  · rwa [rows_slots]

theorem canonical_csv_roundtrip {ipc : ObservationLimits} {csv : DateStream.FromCsv.CsvLimits}
    {name : String} {nullable : Bool} {input : Csv.Bytes} {wire : KBytes}
    {table : Csv.Typed.Table (DateStream.FromCsv.schema name nullable) Csv.Typed.Codecs.Date32.Cell}
    (canonical : Csv.Typed.Codecs.Date32.encode (DateStream.FromCsv.schema name nullable) id table =
      .ok input)
    (written : DateStream.FromCsv.convert ipc csv name nullable input = .ok wire) :
    convert ipc.ipc csv name nullable wire = .ok input := by
  obtain ⟨actual, output, parsed, encoded, _, readback⟩ := csv_roundtrip written
  have tableEq := Except.ok.inj (parsed.symm.trans (Csv.Typed.Codecs.Date32.decode_encode canonical))
  subst actual
  have same := Except.ok.inj (encoded.symm.trans canonical)
  subst output
  exact readback.mpr (DateStream.FromCsv.convert_eq_ok_iff.mp written).1

theorem ipc_roundtrip {ipc : ObservationLimits} {csv : DateStream.FromCsv.CsvLimits} {name : String}
    {nullable : Bool} {input output : KBytes} {wire : Csv.Bytes}
    (exported : convert ipc.ipc csv name nullable input = .ok wire)
    (imported : DateStream.FromCsv.convert ipc csv name nullable wire = .ok output) :
    ∃ slots, DateStream.read ipc.ipc input = .ok (DateStream.Writer.observation name nullable [slots]) ∧
      DateStream.read ipc.ipc output = .ok (DateStream.Writer.observation name nullable [slots]) := by
  obtain ⟨_, slots, observed, _, encoded⟩ := convert_eq_ok_iff.mp exported
  obtain ⟨table, stream, parsed, readback, same, _⟩ := DateStream.FromCsv.convert_readback imported
  have decoded := Csv.Typed.Codecs.Date32.decode_encode encoded
  have tableEq := Except.ok.inj (parsed.symm.trans decoded)
  subst table
  have sameSlots : DateStream.FromCsv.slots (rows name nullable slots) = slots := by
    simp [DateStream.FromCsv.slots, rows, List.map_map, Function.comp_def]
  exact ⟨slots, observed, by rwa [same, sameSlots] at readback⟩

end Silmaril.Proofs.Formats.Arrow.DateStream.ToCsv
