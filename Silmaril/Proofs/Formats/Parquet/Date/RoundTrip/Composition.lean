module

public import Silmaril.Formats.Parquet.Date.RoundTrip.Defs
import Silmaril.Formats.Parquet.Date.Thms
import Silmaril.Formats.Parquet.Date.Events.Thms
import Silmaril.Formats.Parquet.Date.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Date.FromIpc.Multi.Thms
import Silmaril.Formats.Arrow.DateStream.Writer.Thms
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.RoundTrip

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.RoundTrip
open Silmaril.Relational

theorem forward_observes {limits : Date.Limits} {ipcLimits : Arrow.ObservationLimits}
    {wire : Bytes} {ipc : KBytes} (written : Date.Events.ToIpc.convert limits ipcLimits wire = .ok ipc) :
    ∃ observation, ParquetObserves limits wire observation ∧
      Arrow.DateStream.read ipcLimits.ipc ipc = .ok observation.ipc := by
  obtain ⟨schema, trace, column, name, nullable, admitted, eos, _, descriptor, observed⟩ :=
    Date.Events.ToIpc.convert_readback written
  cases opened : Date.openChecked limits wire with
  | error cause =>
    rw [Date.Events.readAll_open_error opened] at admitted
    contradiction
  | ok checked =>
    have canonical := Date.Events.readAll_checked opened
    have sameSchema := congrArg Sigma.fst (Except.ok.inj (admitted.symm.trans canonical))
    change schema = Date.Events.schema checked at sameSchema
    subst schema
    obtain ⟨batches, termination⟩ := trace
    change termination = .eos at eos
    subst termination
    obtain ⟨groups, decoded, exactBatches⟩ :=
      (Date.Events.readAll_eof_iff opened batches).mp admitted
    rw [Date.Events.schema_field] at descriptor
    simp only [Prod.mk.injEq, Date.Events.Kind.date32.injEq] at descriptor
    obtain ⟨rfl, rfl⟩ := descriptor
    refine ⟨_, ⟨checked, groups, opened, decoded, rfl⟩, ?_⟩
    rw [Date.Events.ToIpc.batchSlots, exactBatches] at observed
    simpa only [Observation.ipc, List.map_map, Function.comp_def, Date.Events.batch_slots] using observed

private theorem reverse_observes {readLimits : Arrow.Limits} {writeLimits : Date.FromIpc.Multi.Limits}
    {limits : Date.Limits} {ipc : KBytes} {wire : Bytes}
    (written : Date.FromIpc.Multi.convert readLimits writeLimits limits ipc = .ok wire) :
    ∃ observation, observation.batches ≠ [] ∧ ParquetObserves limits wire observation ∧
      Arrow.DateStream.read readLimits ipc = .ok observation.ipc := by
  obtain ⟨source, plan, checked, groups, read, day, prepared, _, opened, decoded, agrees⟩ :=
    Date.FromIpc.Multi.convert_readback written
  have budget := (Date.FromIpc.Multi.preflight_exact prepared).1
  have nonempty := (Date.FromIpc.Multi.budget_exact budget).1
  unfold Date.FromIpc.Multi.Internal.readGroups at decoded
  have each := List.mapM_eq_ok_iff_forall₂.mp decoded
  have readGroups :
      (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok groups := by
    apply List.mapM_eq_ok_iff_forall₂.mpr
    refine each.imp fun index group success => ?_
    cases result : checked.readGroup limits index <;> simp [result, Except.mapError] at success ⊢
    exact success
  obtain ⟨⟨name, nullable, unit⟩, batches⟩ := source
  change unit = .day at day
  subst unit
  have slots : groups.map (·.civilSlots) = batches := agrees.2.2.2.2.2
  let observation : Observation :=
    ⟨checked.binding.leaf.name, checked.binding.leaf.repetition == some .optional,
      groups.map (·.date32Slots)⟩
  refine ⟨observation, ?_, ⟨checked, groups, opened, readGroups, rfl⟩, ?_⟩
  · intro noGroups
    apply nonempty
    change batches = []
    rw [← slots]
    have empty := List.map_eq_nil_iff.mp noGroups
    simp [empty]
  · have label : checked.binding.leaf.name = name :=
      congrArg Footer.SchemaElement.name agrees.2.2.1
    have flag : (checked.binding.leaf.repetition == some .optional) = nullable := by
      have same := congrArg (fun leaf : Footer.SchemaElement => leaf.repetition == some .optional)
        agrees.2.2.1
      cases nullable <;> simpa [Date.FromIpc.leaf] using same
    rw [read]
    simp [observation, Observation.ipc, Arrow.DateStream.Writer.observation, label, flag,
      List.map_map, Function.comp_def]
    exact slots.symm

theorem sameParquet {limits : Date.Limits} {wire : Bytes} {left right : Observation}
    (a : ParquetObserves limits wire left) (b : ParquetObserves limits wire right) : left = right := by
  obtain ⟨checked, groups, opened, decoded, rfl⟩ := a
  obtain ⟨other, rest, otherOpen, otherRead, rfl⟩ := b
  have same := Except.ok.inj (opened.symm.trans otherOpen)
  subst other
  have same := Except.ok.inj (decoded.symm.trans otherRead)
  subst rest
  rfl

theorem sameIpc {left right : Observation} (same : left.ipc = right.ipc) : left = right := by
  have field := congrArg Arrow.DateStream.Stream.field same
  have days := congrArg (fun stream : Arrow.DateStream.Stream => stream.batches.map
    (List.map (fun slot => slot.bind DateInterop.Date32.ofCivil?))) same
  simp only [Observation.ipc, Arrow.DateStream.Writer.observation_words] at days
  cases left
  cases right
  simp only [Observation.ipc, Arrow.DateStream.Writer.observation, Arrow.DateStream.Field.mk.injEq] at field
  obtain ⟨rfl, rfl, _⟩ := field
  cases days
  rfl

theorem parquet_at {limits : Date.Limits} {wire : Bytes} {observation : Observation}
    (observed : ParquetObserves limits wire observation) :
    ∃ checked, Date.openChecked limits wire = .ok checked ∧
      checked.snapshot.groupCount = observation.batches.length ∧
      ∀ index : Fin observation.batches.length, ∃ group,
        Date.readGroup limits wire index.val = .ok group ∧
        group.date32Slots = observation.batches[index.val] ∧ group.rowCount = observation.batches[index.val].length := by
  obtain ⟨checked, groups, opened, decoded, rfl⟩ := observed
  have ordered := List.mapM_eq_ok_iff_forall₂.mp decoded
  have count : checked.snapshot.groupCount = groups.length := by
    simpa only [List.length_range] using ordered.length_eq
  refine ⟨checked, opened, by simpa only [List.length_map] using count, ?_⟩
  intro index
  have right : index.val < groups.length := by simpa only [List.length_map] using index.isLt
  have left : index.val < (List.range checked.snapshot.groupCount).length :=
    ordered.length_eq.symm ▸ right
  have read := ordered.get left right
  simp only [List.get_eq_getElem, List.getElem_range] at read
  refine ⟨groups[index.val], (checked.readGroup_of_opened opened index.val).symm ▸ read,
    by simp [List.getElem_map], ?_⟩
  rw [List.getElem_map]
  simpa [Date.RowGroup.date32Slots] using (groups[index.val]).column.sized.symm

theorem ipc_roundtrip {inputLimits : Arrow.Limits} {outputLimits : Arrow.ObservationLimits}
    {parquetLimits : Date.Limits} {writerLimits : Date.FromIpc.Multi.Limits}
    {input output : KBytes} {middle : Bytes}
    (toParquet : Date.FromIpc.Multi.convert inputLimits writerLimits parquetLimits input = .ok middle)
    (toIpc : Date.Events.ToIpc.convert parquetLimits outputLimits middle = .ok output) :
    ∃ observation, observation.batches ≠ [] ∧
      Arrow.DateStream.read inputLimits input = .ok observation.ipc ∧
      ParquetObserves parquetLimits middle observation ∧
      Arrow.DateStream.read outputLimits.ipc output = .ok observation.ipc := by
  obtain ⟨start, nonempty, written, readInput⟩ := reverse_observes toParquet
  obtain ⟨finish, reopened, readOutput⟩ := forward_observes toIpc
  cases sameParquet written reopened
  exact ⟨start, nonempty, readInput, written, readOutput⟩

theorem parquet_roundtrip {inputLimits outputLimits : Date.Limits} {ipcLimits : Arrow.ObservationLimits}
    {writerLimits : Date.FromIpc.Multi.Limits} {input output : Bytes} {middle : KBytes}
    (toIpc : Date.Events.ToIpc.convert inputLimits ipcLimits input = .ok middle)
    (toParquet : Date.FromIpc.Multi.convert ipcLimits.ipc writerLimits outputLimits middle = .ok output) :
    ∃ observation, observation.batches ≠ [] ∧ ParquetObserves inputLimits input observation ∧
      Arrow.DateStream.read ipcLimits.ipc middle = .ok observation.ipc ∧
      ParquetObserves outputLimits output observation := by
  obtain ⟨start, readInput, readMiddle⟩ := forward_observes toIpc
  obtain ⟨finish, nonempty, readOutput, rereadMiddle⟩ := reverse_observes toParquet
  cases sameIpc (Except.ok.inj (readMiddle.symm.trans rereadMiddle))
  exact ⟨start, nonempty, readInput, readMiddle, readOutput⟩

end Silmaril.Proofs.Formats.Parquet.Date.RoundTrip
