module

public import Silmaril.Formats.Parquet.Date.ToCsv.Defs
import Silmaril.Formats.Parquet.Date.Events.Thms
public import Silmaril.Formats.Parquet.Date.RoundTrip.Defs
import Silmaril.Formats.Arrow.DateStream.ToCsv.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Date32.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.ToCsv

open Silmaril.Formats Parquet Date.ToCsv
open Silmaril.Relational

private theorem slots_of_batches (checked : Date.Checked) (groups : List Date.RowGroup) :
    Date.Events.ToIpc.batchSlots
      (⟨groups.map (AlignedColumns.ofRows ∘ Date.Events.rows checked), .eos⟩ :
        Arrow.Events.Trace (Date.Events.schema checked) Date.Events.Cell Date.Events.Error)
      ⟨0, Nat.zero_lt_succ 0⟩ = groups.map (·.date32Slots) := by
  simp only [Date.Events.ToIpc.batchSlots, List.map_map, Function.comp_def, Date.Events.batch_slots]

private theorem of_eof {limits : Date.Limits} {name : String} {nullable : Bool}
    {input : Bytes} {checked : Date.Checked} {groups : List Date.RowGroup}
    (opened : Date.openChecked limits input = .ok checked)
    (read : (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok groups)
    (label : checked.binding.leaf.name = name)
    (flag : (checked.binding.leaf.repetition == some .optional) = nullable) :
    readRows limits name nullable input = .ok (groups.map (·.date32Slots)).flatten := by
  unfold readRows
  rw [(Date.Events.readAll_eof_iff opened _).mpr ⟨groups, read, rfl⟩]
  have width : (Date.Events.schema checked).width = 1 := rfl
  simp [width, Date.Events.schema_field, label, flag, slots_of_batches]

theorem readRows_eq_ok_iff {limits : Date.Limits} {name : String} {nullable : Bool}
    {input : Bytes} {slots : Arrow.DateStream.Writer.Column} :
    readRows limits name nullable input = .ok slots ↔
      ∃ batches, Date.RoundTrip.ParquetObserves limits input ⟨name, nullable, batches⟩ ∧
        slots = batches.flatten := by
  constructor
  · intro readSlots
    cases opened : Date.openChecked limits input with
    | error cause =>
      simp [readRows, Date.Events.readAll_open_error opened] at readSlots
    | ok checked =>
      have admitted := Date.Events.readAll_checked opened
      let denoted := Reader.denoteGroups (Date.Events.rowsAt limits checked)
        (List.range checked.snapshot.groupCount)
      change Date.Events.readAll limits input =
        .ok ⟨Date.Events.schema checked, ⟨denoted.1.map AlignedColumns.ofRows, denoted.2⟩⟩ at admitted
      have result := readSlots
      rw [readRows, admitted] at readSlots
      cases terminated : denoted.2 <;> rw [terminated] at readSlots
      case eos =>
        have eof := admitted
        rw [terminated] at eof
        obtain ⟨groups, decoded, _⟩ := (Date.Events.readAll_eof_iff opened _).mp eof
        have width : (Date.Events.schema checked).width = 1 := rfl
        by_cases desc : checked.binding.leaf.name = name ∧
            (checked.binding.leaf.repetition == some .optional) = nullable
        · obtain ⟨label, flag⟩ := desc
          have same := Except.ok.inj ((of_eof opened decoded label flag).symm.trans result)
          exact ⟨_, ⟨checked, groups, opened, decoded, by simp [label, flag]⟩, same.symm⟩
        · simp [width, Date.Events.schema_field, desc] at readSlots
      all_goals simp at readSlots
  · rintro ⟨batches, observed, rfl⟩
    obtain ⟨checked, groups, opened, read, same⟩ := observed
    simp only [Date.RoundTrip.Observation.mk.injEq] at same
    obtain ⟨label, flag, rfl⟩ := same
    exact of_eof opened read label.symm flag.symm

theorem convert_eq_ok_iff {limits : Date.Limits} {csv : Arrow.DateStream.FromCsv.CsvLimits}
    {name : String} {nullable : Bool} {input : Bytes} {wire : Csv.Bytes} :
    convert limits csv name nullable input = .ok wire ↔
      wire.length ≤ csv.maxBytes ∧
      ∃ slots, readRows limits name nullable input = .ok slots ∧ slots.length ≤ csv.maxRows ∧
        Csv.Typed.Codecs.Date32.encode (Arrow.DateStream.FromCsv.schema name nullable) id
          (Arrow.DateStream.ToCsv.rows name nullable slots) = .ok wire := by
  unfold convert
  cases readRows limits name nullable input with
  | error cause => simp [Bind.bind, Except.bind]
  | ok slots =>
    cases encoded : Arrow.DateStream.ToCsv.Internal.encodeColumn csv name nullable slots with
    | error cause =>
      simp [Bind.bind, Except.bind, Except.mapError, encoded,
        ← Arrow.DateStream.ToCsv.Internal.encodeColumn_eq_ok_iff]
    | ok output =>
      simp only [Bind.bind, Except.bind, Except.mapError, encoded, Except.ok.injEq, exists_eq_left']
      rw [← Arrow.DateStream.ToCsv.Internal.encodeColumn_eq_ok_iff, encoded, Except.ok.injEq]

theorem convert_eq_iff {limits : Date.Limits} {csv : Arrow.DateStream.FromCsv.CsvLimits}
    {name : String} {nullable : Bool} {left right : Bytes} {leftWire rightWire : Csv.Bytes}
    (wroteLeft : convert limits csv name nullable left = .ok leftWire)
    (wroteRight : convert limits csv name nullable right = .ok rightWire) :
    leftWire = rightWire ↔ readRows limits name nullable left = readRows limits name nullable right := by
  obtain ⟨_, leftSlots, leftRead, _, leftEncoded⟩ := convert_eq_ok_iff.mp wroteLeft
  obtain ⟨_, rightSlots, rightRead, _, rightEncoded⟩ := convert_eq_ok_iff.mp wroteRight
  rw [leftRead, rightRead, Except.ok.injEq]
  constructor
  · rintro rfl
    have tables := Except.ok.inj ((Csv.Typed.Codecs.Date32.decode_encode leftEncoded).symm.trans
      (Csv.Typed.Codecs.Date32.decode_encode rightEncoded))
    have same := congrArg (Arrow.DateStream.FromCsv.slots (name := name) (nullable := nullable)) tables
    simpa [Arrow.DateStream.FromCsv.slots, Arrow.DateStream.ToCsv.rows, List.map_map,
      Function.comp_def] using same
  · rintro rfl
    exact Except.ok.inj (leftEncoded.symm.trans rightEncoded)

end Silmaril.Proofs.Formats.Parquet.Date.ToCsv
