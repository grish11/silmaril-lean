module

public import Silmaril.Formats.Parquet.Date.FromIpc.Multi.Defs
import Silmaril.Formats.Parquet.Date.Thms
import Silmaril.Prelude.Bytes.Digits.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.FromIpc.Multi

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.FromIpc.Multi
open Silmaril.Formats.Parquet.Date.FromIpc.Multi.Internal

theorem placements_at (start : Nat) {groups : List Group} {index : Nat} {group : Group}
    (found : groups[index]? = some group) :
    let offset := start + ((groups.take index).map (·.size)).sum
    (placements start groups)[index]? = some (group.rows, ⟨offset, offset + group.size⟩) := by
  induction groups generalizing start index with
  | nil => simp at found
  | cons first tail ih =>
    cases index with
    | zero =>
      simp at found
      subst group
      simp [placements]
    | succ index =>
      simpa [placements, Nat.add_assoc] using ih (start + first.size)
        (by simpa using found : tail[index]? = some group)

private theorem header_pos {rows size : Nat} {header : Bytes}
    (encoded : PlainV1Writer.encodeHeader rows size = some header) : 0 < header.length := by
  simp only [PlainV1Writer.encodeHeader, Bind.bind, Option.bind, Pure.pure] at encoded
  split at encoded
  · contradiction
  · dsimp only at encoded
    split at encoded
    · contradiction
    · cases encoded
      simp

private theorem measured_pos {limits : PlainV1Writer.Limits} {input : PlainV1Writer.Input}
    {size : Nat} (measured : FlatInt32Writer.measuredPage limits input = .ok size) : 0 < size := by
  by_cases fits : input.Fits limits
  · cases header : PlainV1Writer.encodeHeader input.numValues input.bodySize with
    | none => simp [FlatInt32Writer.measuredPage, fits, header, throw] at measured
    | some bytes =>
      by_cases cap : limits.headerBytes < bytes.length
      · simp [FlatInt32Writer.measuredPage, fits, header, cap, throw, Bind.bind, Except.bind]
          at measured
      · simp [FlatInt32Writer.measuredPage, fits, header, cap, Pure.pure, Except.pure] at measured
        subst size
        exact Nat.add_pos_left (header_pos header) _
  · simp [FlatInt32Writer.measuredPage, fits, throw, Bind.bind, Except.bind] at measured

private theorem prepare_details {limits : Limits} {nullable : Bool} {batch : Arrow.DateValues.Column}
    {index : Nat} {group : Group} (h : prepare limits nullable batch index = .ok group) :
    group.rows = batch.length ∧
      FlatInt32Writer.measuredPage limits.writer.page group.input = .ok group.size := by
  cases input : Date.FromIpc.Internal.pageInput nullable batch with
  | error cause => simp [prepare, input, Except.mapError, Bind.bind, Except.bind] at h
  | ok page =>
    cases measure : FlatInt32Writer.measuredPage limits.writer.page page with
    | error cause => simp [prepare, input, measure, Except.mapError, Bind.bind, Except.bind] at h
    | ok size =>
      simp [prepare, input, measure, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      subst group
      exact ⟨rfl, measure⟩

private theorem group_rows {groupInputs : List (Arrow.DateValues.Column × Nat)} {groups : List Group}
    (related : List.Forall₂ (fun source group => group.rows = source.1.length) groupInputs groups) :
    groups.map (·.rows) = (groupInputs.map Prod.fst).map List.length := by
  induction related with
  | nil => rfl
  | cons head _ tail => simp [head, tail]

theorem preflight_exact {limits : Limits} {field : Arrow.DateStream.Field} {batches : Batches}
    {plan : Plan} (planned : preflight limits field batches = .ok plan) :
    checkBudget limits field batches = .ok () ∧
    plan.groups.map (·.rows) = batches.map List.length ∧
    (∀ group ∈ plan.groups, 0 < group.size ∧
      FlatInt32Writer.measuredPage limits.writer.page group.input = .ok group.size) ∧
    FlatInt32Writer.Compact.encodeGroups .date (footerLimit limits plan.dataStop)
      [schemaIndex field] (groupIndices field plan.groups) = .ok plan.footer ∧
    plan.footer.length ≤ footerLimit limits plan.dataStop ∧ plan.fileSize ≤ fileLimit limits := by
  cases budget : checkBudget limits field batches with
  | error cause => simp [preflight, budget, Bind.bind, Except.bind] at planned
  | ok result =>
    cases result
    cases prepared : batches.zipIdx.mapM
        (fun (batch, index) => prepare limits field.nullable batch index) with
    | error cause => simp [preflight, budget, prepared, Bind.bind, Except.bind] at planned
    | ok groups =>
      by_cases room : fileLimit limits < (4 + (groups.map (·.size)).sum) + 8
      · simp [preflight, budget, prepared, room, Bind.bind, Except.bind] at planned
      · cases encoded : FlatInt32Writer.Compact.encodeGroups .date (footerLimit limits (4 + (groups.map (·.size)).sum))
            [schemaIndex field] (groupIndices field groups) with
        | error cause =>
          simp [preflight, budget, prepared, room, encoded, Except.mapError,
            Bind.bind, Except.bind] at planned
        | ok footer =>
          by_cases fits : footerLimit limits (4 + (groups.map (·.size)).sum) < footer.length
          · simp [preflight, budget, prepared, room, encoded, fits, Except.mapError,
              Bind.bind, Except.bind] at planned
          · simp [preflight, budget, prepared, room, encoded, fits, Except.mapError,
              Bind.bind, Except.bind] at planned
            subst plan
            have relates := List.mapM_eq_ok_iff_forall₂.mp prepared
            have details := relates.imp fun _ _ h => prepare_details h
            have rows := group_rows (details.imp fun _ _ h => h.1)
            rw [List.zipIdx_map_fst] at rows
            refine ⟨rfl, rows, ?_, encoded, Nat.le_of_not_gt fits, ?_⟩
            · intro group member
              obtain ⟨index, inGroups, rfl⟩ := List.mem_iff_getElem.mp member
              have inBatches : index < batches.zipIdx.length := details.length_eq.symm ▸ inGroups
              have measured := (details.get inBatches inGroups).2
              exact ⟨measured_pos measured, measured⟩
            · have cap := Nat.le_of_not_gt fits
              unfold footerLimit at cap
              simp [Plan.fileSize, Plan.dataStop]
              omega

theorem budget_exact {limits : Limits} {field : Arrow.DateStream.Field} {batches : Batches}
    (checked : checkBudget limits field batches = .ok ()) :
    batches ≠ [] ∧ batches.length ≤ limits.maxGroups ∧
      batches.length ≤ limits.writer.footer.compact.maxCollectionSize ∧
      totalRows batches ≤ limits.maxTotalRows ∧ totalRows batches < 2^63 ∧
      0 < limits.writer.maxColumns ∧ 2 ≤ limits.writer.footer.compact.maxCollectionSize ∧
      field.name.utf8ByteSize ≤ limits.writer.footer.compact.maxBinaryBytes := by
  simp only [checkBudget] at checked
  split at checked
  · contradiction
  split at checked
  · contradiction
  split at checked
  · contradiction
  split at checked
  · contradiction
  rename_i nonempty notMany notRows schema
  simp_all [Bool.or_eq_true, List.isEmpty_iff, Nat.pos_iff_ne_zero]

theorem emit_extent {limits : Limits} {plan : Plan} {wire : Bytes}
    (written : emit limits plan = .ok wire) : wire.length = plan.fileSize := by
  cases paged : plan.groups.zipIdx.mapM (fun (group, index) =>
      (PlainV1Writer.emit limits.writer.page group.input).mapError (.page index : _ → Error)) with
  | error cause => simp [emit, paged, Bind.bind, Except.bind] at written
  | ok pages =>
    by_cases same : pages.map (·.wire.length) = plan.groups.map (·.size)
    · simp [emit, paged, same, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
      subst wire
      simp [Plan.fileSize, Plan.dataStop, Footer.magic, KBytes.length_unpack, same, Nat.add_assoc]
    · simp [emit, paged, same, Bind.bind, Except.bind] at written

private theorem certify_ok {limits : Date.Limits} {wire output : Bytes}
    {field : Arrow.DateStream.Field} {batches : Batches}
    (certified : certify limits wire field batches = .ok output) :
    wire = output ∧ ∃ checked groups, Date.openChecked limits output = .ok checked ∧
      readGroups limits checked = .ok groups ∧ Matches checked groups field batches := by
  cases opened : Date.openChecked limits wire with
  | error cause => simp [certify, opened, Except.mapError, Bind.bind, Except.bind] at certified
  | ok checked =>
    cases decoded : readGroups limits checked with
    | error cause => simp [certify, opened, decoded, Except.mapError, Bind.bind, Except.bind] at certified
    | ok groups =>
      by_cases agrees : Matches checked groups field batches
      · simp [certify, opened, decoded, agrees, Except.mapError, Bind.bind, Except.bind] at certified
        subst output
        exact ⟨rfl, checked, groups, opened, decoded, agrees⟩
      · simp [certify, opened, decoded, agrees, Except.mapError, Bind.bind, Except.bind] at certified

theorem convert_readback {inputLimits : Arrow.Limits} {writerLimits : Limits} {readbackLimits : Date.Limits}
    {input : KBytes} {wire : Bytes} (written : convert inputLimits writerLimits readbackLimits input = .ok wire) :
    ∃ source plan checked groups,
      Arrow.DateStream.read inputLimits input = .ok source ∧ source.field.unit = .day ∧
      preflight writerLimits source.field source.batches = .ok plan ∧
      wire.length = plan.fileSize ∧ Date.openChecked readbackLimits wire = .ok checked ∧
      readGroups readbackLimits checked = .ok groups ∧ Matches checked groups source.field source.batches := by
  cases read : Arrow.DateStream.read inputLimits input with
  | error cause => simp [convert, read, Except.mapError, Bind.bind, Except.bind] at written
  | ok source =>
    by_cases unit : source.field.unit = .day
    · cases planned : preflight writerLimits source.field source.batches with
      | error cause => simp [convert, read, unit, planned, Except.mapError, Bind.bind, Except.bind] at written
      | ok plan =>
        cases emitted : emit writerLimits plan with
        | error cause =>
          simp [convert, read, unit, planned, emitted, Except.mapError, Bind.bind, Except.bind] at written
        | ok raw =>
          simp [convert, read, unit, planned, emitted, Except.mapError, Bind.bind, Except.bind] at written
          obtain ⟨rfl, checked, groups, opened, decoded, agrees⟩ := certify_ok written
          exact ⟨source, plan, checked, groups, rfl, unit, planned, emit_extent emitted, opened, decoded, agrees⟩
    · simp [convert, read, unit, Except.mapError, Bind.bind, Except.bind] at written

theorem readback_at {limits : Date.Limits} {checked : Date.Checked} {groups : List Date.RowGroup}
    {field : Arrow.DateStream.Field} {batches : Batches}
    (read : readGroups limits checked = .ok groups)
    (agrees : Matches checked groups field batches) (index : Fin batches.length) :
    ∃ group, checked.readGroup limits index.val = .ok group ∧
      group.rowCount = batches[index.val].length ∧ group.civilSlots = batches[index.val] ∧
      group.date32Slots = batches[index.val].map (fun slot => slot.bind DateInterop.Date32.ofCivil?) := by
  unfold readGroups at read
  have ordered := List.mapM_eq_ok_iff_forall₂.mp read
  have inRange : index.val < (List.range checked.snapshot.groupCount).length := by
    simp [agrees.1]
  have inGroups : index.val < groups.length := ordered.length_eq ▸ inRange
  let group := groups[index.val]
  have atIndex := ordered.get inRange inGroups
  simp only [List.get_eq_getElem, List.getElem_range] at atIndex
  have decoded : checked.readGroup limits index.val = .ok group := by
    cases eq : checked.readGroup limits index.val with
    | error cause => simp [eq, Except.mapError] at atIndex
    | ok row =>
      simp [eq, Except.mapError, group] at atIndex ⊢
      exact atIndex
  have rowCount := congrArg (fun xs : List Nat => xs[index.val]?) agrees.2.2.2.2.1
  have slots := congrArg (fun xs : Batches => xs[index.val]?) agrees.2.2.2.2.2
  simp [List.getElem?_eq_getElem inGroups] at rowCount slots
  refine ⟨group, decoded, rowCount, slots, ?_⟩
  rw [← group.date32_civil, slots]

end Silmaril.Proofs.Formats.Parquet.Date.FromIpc.Multi
