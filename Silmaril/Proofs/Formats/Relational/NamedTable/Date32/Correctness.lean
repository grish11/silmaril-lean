module

public import Silmaril.Formats.Relational.NamedTable.Date32.Defs
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Formats.Parquet.Date.Events.Thms
import Silmaril.Formats.Arrow.DateStream.Thms
import Silmaril.Formats.DateInterop.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.Date32

open Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (importCollected importCollected_ok_iff
  importArrow importArrow_ok_iff)
open Silmaril.Formats.Relational.NamedTable.Date32
open Arrow
open Silmaril.Numeric.Gregorian (CivilDate)

private theorem civil_slot_of_wire {view : DateValues.View} {index : Nat} {date : Option CivilDate}
    (wire : DateValues.SlotWire .day view index date) :
    ∃ valid word,
      Body.validAt view.validity (view.start + index) = some valid ∧
      view.values.readLE (4 * (view.start + index)) 4 = some word ∧
      date = (if valid then some (Int32.ofNat word) else none).map DateInterop.Date32.toCivil := by
  obtain ⟨valid, word, bit, bytes, observed⟩ := wire
  refine ⟨valid, word, bit, bytes, ?_⟩
  cases valid
  · exact observed
  · obtain ⟨civil, parsed, rfl⟩ := observed
    exact parsed.symm

theorem recover_wire_slot {view : DateValues.View} {index : Nat} {date : Option CivilDate}
    (wire : DateValues.SlotWire .day view index date) :
    ∃ valid word,
      Body.validAt view.validity (view.start + index) = some valid ∧
      view.values.readLE (4 * (view.start + index)) 4 = some word ∧
      recover date = .ok (if valid then some (Int32.ofNat word) else none) := by
  obtain ⟨valid, word, bit, bytes, observed⟩ := civil_slot_of_wire wire
  exact ⟨valid, word, bit, bytes, by cases valid <;> simp [observed, recover]⟩

private theorem recover_roundtrip (slots : List Slot) :
    (slots.map (Option.map DateInterop.Date32.toCivil)).mapM recover = .ok slots := by
  induction slots with
  | nil => rfl
  | cons slot slots ih => cases slot <;> simp [recover, List.mapM_cons, ih] <;> rfl

private theorem civil_image_of_column {view : DateValues.View} {indices : List Nat}
    {dates : DateValues.Column} (wire : List.Forall₂ (DateValues.SlotWire .day view) indices dates) :
    ∃ slots : List Slot, dates = slots.map (Option.map DateInterop.Date32.toCivil) := by
  induction wire with
  | nil => exact ⟨[], rfl⟩
  | cons slotWire _ ih =>
    obtain ⟨tail, tailEq⟩ := ih
    obtain ⟨valid, word, _, _, observed⟩ := civil_slot_of_wire slotWire
    exact ⟨(if valid then some (Int32.ofNat word) else none) :: tail, by rw [List.map_cons, observed, tailEq]⟩

private theorem civil_image_of_batches {limits : Arrow.Limits} {input : KBytes}
    {field : DateStream.Field} (day : field.unit = .day)
    {remaining offset : Nat} {batches : List DateValues.Column}
    (wire : DateStream.BatchesWire limits input field remaining offset batches) :
    ∃ slots : List Slot, batches.flatten = slots.map (Option.map DateInterop.Date32.toCivil) := by
  induction wire with
  | eos => exact ⟨[], rfl⟩
  | next _ batch _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, column⟩ :=
      (DateStream.readBatch_iff _ _ _ _ _ _ _).mp batch
    rw [show field.decoder = .day by simp [DateStream.Field.decoder, day, DateBatch.dateDecoder]]
      at column
    obtain ⟨head, headEq⟩ := civil_image_of_column column.1
    obtain ⟨tail, tailEq⟩ := ih
    exact ⟨head ++ tail, by simp [headEq, tailEq]⟩

theorem read_date32_slots {limits : Arrow.Limits} {input : KBytes} {stream : DateStream.Stream}
    (read : DateStream.read limits input = .ok stream) (day : stream.field.unit = .day) :
    ∃ slots : List Slot,
      stream.batches.flatten = slots.map (Option.map DateInterop.Date32.toCivil) ∧
      stream.batches.flatten.mapM recover = .ok slots := by
  obtain ⟨_, _, _, wire⟩ := (DateStream.read_iff limits input stream).mp read
  obtain ⟨slots, image⟩ := civil_image_of_batches day wire
  exact ⟨slots, image, image ▸ recover_roundtrip slots⟩

theorem schema_eq_iff {left right : String} {nullableLeft nullableRight : Bool} :
    schema left nullableLeft = schema right nullableRight ↔
      left = right ∧ nullableLeft = nullableRight := by
  constructor
  · intro equal
    have labels := congrArg (fun s : Scan.Schema String Parquet.Date.Events.Kind => List.ofFn s.kind) equal
    simpa [schema, List.ofFn_succ] using labels
  · rintro ⟨rfl, rfl⟩
    rfl

variable {Name : Type*} [DecidableEq Name]
variable {db next : Database Name} {name : Name} {field : String} {nullable : Bool}
variable {parquetLimits : Parquet.Date.Limits} {parquet : Bytes}
variable {ipcLimits : Arrow.Limits} {ipc : KBytes}

private theorem parquet_collect_of_groups {checked : Parquet.Date.Checked} {groups : List Parquet.Date.RowGroup}
    (opened : Parquet.Date.openChecked parquetLimits parquet = .ok checked)
    (decoded : (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquetLimits) = .ok groups) :
    (Parquet.Date.Events.readAll parquetLimits parquet).collect =
      .ok ⟨⟨schema checked.binding.leaf.name (checked.binding.leaf.repetition == some .optional),
        rows checked.binding.leaf.name (checked.binding.leaf.repetition == some .optional)
          (groups.flatMap Parquet.Date.RowGroup.date32Slots)⟩, .eos⟩ := by
  rw [(Parquet.Date.Events.readAll_eof_iff opened _).mpr ⟨groups, decoded, rfl⟩]
  simp [Events.EventStream.collect, Events.Trace.collect, Events.Trace.rows, Parquet.Date.Events.rows,
    rows, Except.map, List.flatMap_map, List.map_flatMap, Function.comp_def]
  exact ⟨rfl, HEq.rfl⟩

theorem importParquet_ok_iff :
    importParquet db name field nullable parquetLimits parquet = .ok next ↔
      db name = none ∧ ∃ checked groups,
        Parquet.Date.openChecked parquetLimits parquet = .ok checked ∧
        (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquetLimits) = .ok groups ∧
        checked.binding.leaf.name = field ∧ (checked.binding.leaf.repetition == some .optional) = nullable ∧
        next = Function.update db name (some ⟨schema field nullable,
          rows field nullable (groups.flatMap Parquet.Date.RowGroup.date32Slots)⟩) := by
  constructor
  · intro imported
    obtain ⟨vacant, table, collected, updated⟩ := (importArrow_ok_iff ..).mp imported
    cases opened : Parquet.Date.openChecked parquetLimits parquet with
    | error cause =>
      rw [Parquet.Date.Events.readAll_open_error opened] at collected
      cases collected
    | ok checked =>
      have events := Parquet.Date.Events.readAll_checked opened
      have observed := collected
      rw [events] at observed
      have equalSchema : Parquet.Date.Events.schema checked = schema field nullable :=
        congrArg (fun o => o.table.schema) (Except.ok.inj observed)
      have endOfStream :
          (Parquet.Reader.denoteGroups (Parquet.Date.Events.rowsAt parquetLimits checked)
            (List.range checked.snapshot.groupCount)).2 = .eos :=
        congrArg Events.Observation.termination (Except.ok.inj observed)
      rw [endOfStream] at events
      obtain ⟨groups, decoded, _⟩ := (Parquet.Date.Events.readAll_eof_iff opened _).mp events
      have labels : checked.binding.leaf.name = field ∧
          (checked.binding.leaf.repetition == some .optional) = nullable :=
        schema_eq_iff.mp equalSchema
      have complete := parquet_collect_of_groups opened decoded
      rw [labels.1, labels.2, collected] at complete
      have sameTable := congrArg
        (fun o => (⟨o.table.schema, o.table.rows⟩ : Σ s, Scan.Table s Parquet.Date.Events.Cell))
        (Except.ok.inj complete)
      refine ⟨vacant, checked, groups, rfl, decoded, labels.1, labels.2, updated.trans ?_⟩
      change Function.update db name (some ⟨schema field nullable, table⟩) = _
      rw [sameTable]
  · rintro ⟨vacant, checked, groups, opened, decoded, label, repetition, rfl⟩
    apply (importArrow_ok_iff ..).mpr
    refine ⟨vacant, _, ?_, rfl⟩
    have complete := parquet_collect_of_groups opened decoded
    rw [label, repetition] at complete
    exact complete

theorem importIpc_ok_iff :
    importIpc db name field nullable ipcLimits ipc = .ok next ↔
      db name = none ∧ ∃ stream slots,
        DateStream.read ipcLimits ipc = .ok stream ∧
        stream.field = ⟨field, nullable, .day⟩ ∧
        stream.batches.flatten = slots.map (Option.map DateInterop.Date32.toCivil) ∧
        next = Function.update db name (some ⟨schema field nullable, rows field nullable slots⟩) := by
  constructor
  · intro imported
    cases vacant : db name with
    | some current => simp [importIpc, vacant] at imported
    | none =>
      cases read : DateStream.read ipcLimits ipc with
      | error reason => cases reason <;> simp [importIpc, vacant, read] at imported
      | ok stream =>
        by_cases day : stream.field.unit = .day
        · obtain ⟨slots, image, recovered⟩ := read_date32_slots read day
          simp only [importIpc, vacant, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, read, day,
            ne_eq, not_true_eq_false, recovered] at imported
          obtain ⟨_, table, observed, updated⟩ := (importCollected_ok_iff ..).mp imported
          have equalTable := congrArg
            (fun o => (⟨o.table.schema, o.table.rows⟩ : Σ s, Scan.Table s Parquet.Date.Events.Cell))
            (Except.ok.inj observed)
          have equalSchema : schema stream.field.name stream.field.nullable = schema field nullable :=
            congrArg Sigma.fst equalTable
          obtain ⟨label, repetition⟩ := schema_eq_iff.mp equalSchema
          have exactField : stream.field = ⟨field, nullable, .day⟩ := by
            cases actual : stream.field with
            | mk actualName actualNullable actualUnit =>
              rw [actual] at label repetition day
              cases label
              cases repetition
              cases day
              rfl
          refine ⟨rfl, stream, slots, rfl, exactField, image, updated.trans ?_⟩
          rw [← equalTable, label, repetition]
        · simp [importIpc, vacant, read, day] at imported
  · rintro ⟨vacant, stream, slots, read, exactField, image, rfl⟩
    have recovered := image ▸ recover_roundtrip slots
    have inserted := (importCollected_ok_iff (Error := IpcError) db _ name (schema field nullable)
      (.ok ⟨⟨schema field nullable, rows field nullable slots⟩, .eos⟩)).mpr ⟨vacant, _, rfl, rfl⟩
    have label : stream.field.name = field := congrArg DateStream.Field.name exactField
    have repetition : stream.field.nullable = nullable := congrArg DateStream.Field.nullable exactField
    simp [importIpc, vacant, read, exactField, recovered]
    rw [label, repetition]
    exact inserted

theorem imports_equal_of_rows
    {checked : Parquet.Date.Checked} {groups : List Parquet.Date.RowGroup}
    {stream : DateStream.Stream}
    (vacant : db name = none)
    (opened : Parquet.Date.openChecked parquetLimits parquet = .ok checked)
    (decoded : (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquetLimits) = .ok groups)
    (label : checked.binding.leaf.name = field)
    (repetition : (checked.binding.leaf.repetition == some .optional) = nullable)
    (read : DateStream.read ipcLimits ipc = .ok stream)
    (exactField : stream.field = ⟨field, nullable, .day⟩)
    (sameRows : stream.batches.flatten =
      (groups.flatMap Parquet.Date.RowGroup.date32Slots).map (Option.map DateInterop.Date32.toCivil)) :
    ∃ next, importParquet db name field nullable parquetLimits parquet = .ok next ∧
      importIpc db name field nullable ipcLimits ipc = .ok next :=
  ⟨_, importParquet_ok_iff.mpr ⟨vacant, checked, groups, opened, decoded, label, repetition, rfl⟩,
    importIpc_ok_iff.mpr ⟨vacant, stream, _, read, exactField, sameRows, rfl⟩⟩

theorem importParquet_group_error {checked : Parquet.Date.Checked}
    {before after : List Nat} {index : Nat} {groups : List Parquet.Date.RowGroup} {cause : Parquet.Date.Error}
    (vacant : db name = none)
    (opened : Parquet.Date.openChecked parquetLimits parquet = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup parquetLimits) = .ok groups)
    (failed : checked.readGroup parquetLimits index = .error cause) :
    importParquet db name field nullable parquetLimits parquet = .error (.readError (.groupFailure index cause)) := by
  rw [importParquet, Parquet.Date.Events.readAll_first_error opened split earlier failed]
  simp [importArrow, importCollected, vacant, Events.EventStream.collect, Events.Trace.collect, Except.map]

end Silmaril.Proofs.Formats.Relational.NamedTable.Date32
