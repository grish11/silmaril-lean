module

public import Silmaril.Formats.Relational.NamedTable.MixedIpc.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Stream.Thms
public import Silmaril.Formats.Relational.NamedTable.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc

open Silmaril.Formats
open Silmaril.Formats.Arrow
open Silmaril.Formats.Relational.NamedTable
open Silmaril.Formats.Relational.NamedTable.MixedIpc

theorem descriptor_exact {fields : List MixedFlat.Field} {descriptor : Descriptor}
    (found : Descriptor.ofFields fields = some descriptor) : fields = descriptor.fields := by
  unfold Descriptor.ofFields at found
  split at found
  · cases found
    rfl
  · cases found
    rfl
  · contradiction

private theorem intSlot_exact {input : Option Arrow.Value} {output : Option Int32}
    (parsed : intSlot input = some output) : input = output.map Arrow.Value.int32 := by
  cases input with
  | none => simp_all [intSlot]
  | some value =>
    cases value <;> simp_all [intSlot]

private theorem intSlots_exact {input : Arrow.Column} {output : List (Option Int32)}
    (parsed : input.mapM intSlot = some output) : input = output.map (Option.map Arrow.Value.int32) := by
  induction input generalizing output with
  | nil => simpa using parsed
  | cons head tail ih =>
    cases hs : intSlot head with
    | none => simp [List.mapM_cons, hs] at parsed
    | some first =>
      cases ts : tail.mapM intSlot with
      | none => simp [List.mapM_cons, hs, ts] at parsed
      | some rest =>
        simp [List.mapM_cons, hs, ts] at parsed
        subst output
        simp [intSlot_exact hs, ih ts]

theorem batchPairs_exact {descriptor : Descriptor} {batch : MixedFlat.Stream.Batch} {pairs : List Pair}
    (found : batchPairs descriptor batch = some pairs) :
    pairs.length = batch.observed.rowCount ∧
      ∃ bytes : List (Option KBytes),
        pairs.map Prod.snd = bytes.map (Option.map KBytes.toList) ∧
        let integer := (descriptor.intField, MixedFlat.Column.primitive
          (pairs.map fun pair => pair.1.map Arrow.Value.int32))
        let binary := (descriptor.viewField, MixedFlat.Column.binaryView bytes)
        batch.observed.columns = if descriptor.viewFirst then [binary, integer] else [integer, binary] := by
  unfold batchPairs at found
  simp only [bind, Option.bind] at found
  split at found
  · contradiction
  next fields =>
    split at found
    next intField ints viewField bytes ordered =>
      cases decode : ints.mapM intSlot with
      | none => simp [decode] at found
      | some values =>
        simp only [decode] at found
        split at found
        next lengths =>
          cases found
          have same : values.length = bytes.length := lengths.1.trans lengths.2.symm
          have hInt := List.map_fst_zip (l₁ := values) (l₂ := bytes.map (Option.map KBytes.toList))
            (by simpa using same.le)
          have hBin := List.map_snd_zip (l₁ := values) (l₂ := bytes.map (Option.map KBytes.toList))
            (by simpa using same.ge)
          refine ⟨by simp [List.length_zip, same, lengths.2], bytes, hBin, ?_⟩
          have integerExact : ints = (values.zip (bytes.map (Option.map KBytes.toList))).map
              (fun pair => pair.1.map Arrow.Value.int32) := by
            simpa only [List.map_map, Function.comp_def] using
              (intSlots_exact decode).trans (congrArg (List.map (Option.map Arrow.Value.int32)) hInt.symm)
          cases order : descriptor.viewFirst
          · simp [order] at ordered
            simp [Descriptor.fields, order, ordered] at fields
            simp [ordered, fields.1, fields.2, integerExact]
          · simp [order, List.reverse_eq_iff] at ordered
            simp [Descriptor.fields, order, ordered] at fields
            simp [ordered, fields.2, fields.1, integerExact]
        · contradiction
    · contradiction

private theorem prepareBatches_exact (descriptor : Descriptor)
    (batches : List MixedFlat.Stream.Batch) (index : Nat) (pairs : List (List Pair))
    (ok : prepareBatches descriptor index batches = .ok pairs) :
    List.Forall₂ (fun batch rows => batchPairs descriptor batch = some rows) batches pairs := by
  induction batches generalizing index pairs with
  | nil =>
    cases ok
    exact .nil
  | cons batch rest ih =>
    cases head : batchPairs descriptor batch with
    | none => simp [prepareBatches, head, throw] at ok
    | some rows =>
      cases tail : prepareBatches descriptor (index + 1) rest with
      | error error => simp [prepareBatches, head, tail, bind, Except.bind] at ok
      | ok rowLists =>
        simp [prepareBatches, head, tail, bind, Except.bind, pure, Except.pure] at ok
        subst pairs
        exact .cons head (ih (index + 1) rowLists tail)

theorem read_exact {limits : MixedIpc.Limits} {input : KBytes} {prepared : Prepared}
    (read : MixedIpc.read limits input = .ok prepared) :
    input.len ≤ limits.inputBytes ∧
    ∃ source : MixedFlat.Stream.Observed, MixedFlat.Stream.read limits.mixed input = .ok source ∧
      source.fields = prepared.descriptor.fields ∧
      List.Forall₂ (fun batch pairs => batchPairs prepared.descriptor batch = some pairs)
        source.batches prepared.batches := by
  unfold MixedIpc.read at read
  by_cases cap : input.len > limits.inputBytes
  · simp [cap] at read
  refine ⟨Nat.le_of_not_gt cap, ?_⟩
  cases decoded : MixedFlat.Stream.read limits.mixed input with
  | error cause => simp [cap, decoded, Except.mapError, Except.bind] at read
  | ok source =>
    refine ⟨source, rfl, ?_⟩
    simp [cap, decoded, Except.mapError, Except.bind] at read
    cases found : Descriptor.ofFields source.fields with
    | none => simp [prepare, found, throw] at read
    | some descriptor =>
      cases parsed : prepareBatches descriptor 0 source.batches with
      | error cause => simp [prepare, found, parsed, bind, Except.bind] at read
      | ok pairs =>
        simp [prepare, found, parsed, bind, Except.bind, pure, Except.pure] at read
        subst prepared
        exact ⟨descriptor_exact found, prepareBatches_exact descriptor _ 0 _ parsed⟩

open Silmaril.Relational in
theorem importIpc_ok_iff {Name : Type*} [DecidableEq Name]
    (db next : Database Name) (name : Name) (expected : Descriptor) (limits : MixedIpc.Limits) (input : KBytes) :
    importIpc db name expected limits input = .ok next ↔
      db name = none ∧ ∃ prepared : Prepared, MixedIpc.read limits input = .ok prepared ∧
        prepared.table.schema = expected.schema ∧
        next = Function.update db name (some ⟨prepared.table.schema, prepared.table.rows⟩) := by
  have unchanged : ∀ result : Except (ImportError MixedIpc.Error) (Database Name),
      result.mapError classify = .ok next ↔ result = .ok next := by
    intro result
    cases result <;> simp [Except.mapError]
  unfold importIpc
  rw [unchanged, importCollected_ok_iff]
  cases observation : MixedIpc.read limits input with
  | error cause => simp [collect, observation, Except.map]
  | ok prepared =>
    simp only [collect, observation, Except.map, Except.ok.injEq]
    constructor
    · rintro ⟨vacant, rows, equal, update⟩
      have equalTable : prepared.table = ⟨expected.schema, rows⟩ := congrArg Events.Observation.table equal
      refine ⟨vacant, prepared, rfl, congrArg Scan.Observation.schema equalTable, ?_⟩
      change next = (fun (table : Scan.Observation Label Cell) =>
        Function.update db name (some ⟨table.schema, table.rows⟩)) prepared.table
      rw [equalTable]
      exact update
    · rintro ⟨vacant, actual, rfl, schema, update⟩
      generalize ht : prepared.table = table at schema update ⊢
      cases table with
      | mk tableSchema rows =>
        change tableSchema = expected.schema at schema
        subst tableSchema
        exact ⟨vacant, rows, rfl, update⟩

theorem schema_columns (descriptor : Descriptor) :
    List.ofFn descriptor.schema.kind =
      (if descriptor.viewFirst then [(descriptor.binary, .binaryView), (descriptor.integer, .int32)]
        else [(descriptor.integer, .int32), (descriptor.binary, .binaryView)]) := by
  cases descriptor with
  | mk order integer binary =>
    cases order <;> simp [Descriptor.schema, List.ofFn_succ]

theorem schema_injective : Function.Injective Descriptor.schema := by
  intro left right equal
  have columns := congrArg (fun schema => List.ofFn schema.kind) equal
  rw [schema_columns, schema_columns] at columns
  cases left with
  | mk leftOrder leftInteger leftBinary =>
    cases right with
    | mk rightOrder rightInteger rightBinary =>
      cases leftOrder <;> cases rightOrder <;> simp_all

theorem importIpc_eq_of_table {Name : Type*} [DecidableEq Name]
    (db : Database Name) (name : Name) (expected : Descriptor)
    {limits : MixedIpc.Limits} {left right : KBytes} {a b : Prepared}
    (leftRead : MixedIpc.read limits left = .ok a) (rightRead : MixedIpc.read limits right = .ok b)
    (equal : a.table = b.table) :
    importIpc db name expected limits left = importIpc db name expected limits right := by
  simp [importIpc, collect, leftRead, rightRead, Except.map, equal]

theorem importIpc_openFailure {Name : Type*} [DecidableEq Name]
    {db : Database Name} {name : Name} (vacant : db name = none) (expected : Descriptor)
    {limits : MixedIpc.Limits} {input : KBytes} {cause : MixedIpc.Error}
    (failed : MixedIpc.read limits input = .error cause) :
    importIpc db name expected limits input = .error (classify (.openError cause)) := by
  simp [importIpc, collect, failed, importCollected, vacant, Except.map, Except.mapError]

theorem importIpc_readFailure {Name : Type*} [DecidableEq Name]
    {db : Database Name} {name : Name} (vacant : db name = none) (expected : Descriptor)
    {limits : MixedIpc.Limits} {input : KBytes} (within : input.len ≤ limits.inputBytes)
    {index : Nat} {cause : MixedFlat.Stream.BatchError}
    (failed : MixedFlat.Stream.read limits.mixed input = .error (.batch index cause)) :
    importIpc db name expected limits input = .error (.readError (.reader (.batch index cause))) := by
  refine importIpc_openFailure vacant expected (cause := .reader (.batch index cause)) ?_
  simp [MixedIpc.read, Nat.not_lt.mpr within, failed, Except.mapError, Except.bind]

end Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc
