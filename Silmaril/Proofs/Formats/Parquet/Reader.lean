module

public import Silmaril.Formats.Parquet.Reader.Defs
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Semantics.Relational.Scan.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Reader

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet.Reader

variable {Group Id Kind Error : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

private theorem pull_eq (groups : List Group)
    (readGroup : Group → Except Error (RowGroup schema Value)) (close : List Group → Except Error Unit)
    (seen : List (Events.Batch schema Value)) :
    Events.BatchReader.read.pull (batchReader (id : OpenResult Group Id Value Error → _))
        schema (groups.length + 1) ⟨groups, readGroup, close⟩ seen =
      ⟨seen.reverse ++ (denoteGroups readGroup groups).1.map AlignedColumns.ofRows,
        (denoteGroups readGroup groups).2⟩ := by
  induction groups generalizing seen with
  | nil => simp [Events.BatchReader.read.pull, batchReader, denoteGroups]
  | cons group rest ih =>
    rw [List.length_cons, Nat.succ_add, Events.BatchReader.read.pull]
    cases decoded : readGroup group with
    | error error =>
      simp [batchReader, Except.map, denoteGroups, decoded]
    | ok rows =>
      simpa [batchReader, Except.map, denoteGroups, decoded, List.reverse_cons,
        List.append_assoc] using ih (AlignedColumns.ofRows rows :: seen)

theorem readAll_opened (source : Source Group schema Value Error) :
    readAll (.ok ⟨schema, source⟩) = .ok ⟨schema,
      ⟨(denoteGroups source.readGroup source.groups).1.map AlignedColumns.ofRows,
        (denoteGroups source.readGroup source.groups).2⟩⟩ := by
  cases source with
  | mk groups readGroup close =>
    have trace := pull_eq groups readGroup close []
    simp only [List.reverse_nil, List.nil_append] at trace
    exact congrArg (fun t => (Except.ok ⟨schema, t⟩ : Events.EventStream Id Value Error)) trace

theorem collect_readAll (opened : OpenResult Group Id Value Error) :
    (readAll opened).collect = denote opened := by
  rcases opened with error | ⟨schema, source⟩
  · rfl
  · rw [readAll_opened]
    simp [denote, Except.map, Events.EventStream.collect, Events.Trace.collect, Events.Trace.rows,
      List.flatMap_map, Function.comp_def]

private theorem scanGroups_skip (projection : Scan.Projection schema) (predicate : Scan.Predicate schema Value)
    (readGroup : Group → Except Error (RowGroup schema Value))
    (before after : List Group) (group : Group) {rows : RowGroup schema Value}
    (decoded : readGroup group = .ok rows)
    (rejected : ∀ row ∈ rows, (predicate row).getD false = false) :
    (projection.scan predicate (denoteGroups readGroup (before ++ group :: after)).1.flatten,
      (denoteGroups readGroup (before ++ group :: after)).2) =
    (projection.scan predicate (denoteGroups readGroup (before ++ after)).1.flatten,
      (denoteGroups readGroup (before ++ after)).2) := by
  have selected : Scan.select predicate rows = [] :=
    List.filter_eq_nil_iff.mpr fun row mem => by simp [rejected row mem]
  have scanned : projection.scan predicate rows = [] := by
    simp [Scan.Projection.scan, Scan.Projection.project, selected]
  induction before with
  | nil => simp [denoteGroups, decoded, Scan.Projection.scan_append, scanned]
  | cons first before ih =>
    cases firstDecoded : readGroup first with
    | error error => simp [denoteGroups, firstDecoded]
    | ok firstRows =>
      have extended := congrArg
        (fun out : Scan.Table projection.schema Value × Events.Termination Error =>
          (projection.scan predicate firstRows ++ out.1, out.2)) ih
      simpa [denoteGroups, firstDecoded, Scan.Projection.scan_append] using extended

theorem scan_readAll_skipGroup (source : Source Group schema Value Error)
    (before after : List Group) (group : Group)
    (projection : (s : Scan.Schema Id Kind) → Scan.Projection s)
    (predicate : (s : Scan.Schema Id Kind) → Scan.Predicate s Value)
    (split : source.groups = before ++ group :: after) {rows : RowGroup schema Value}
    (decoded : source.readGroup group = .ok rows)
    (rejected : ∀ row ∈ rows, (predicate schema row).getD false = false) :
    Events.EventStream.Equivalent
      ((readAll (.ok ⟨schema, source⟩)).scan projection predicate)
      ((readAll (.ok ⟨schema, { source with groups := before ++ after }⟩)).scan projection predicate) := by
  unfold Events.EventStream.Equivalent
  rw [Events.EventStream.collect_scan, Events.EventStream.collect_scan, collect_readAll, collect_readAll]
  simpa [denote, Except.map, split] using congrArg
    (fun out : Scan.Table (projection schema).schema Value × Events.Termination Error =>
      (Except.ok ⟨⟨(projection schema).schema, out.1⟩, out.2⟩ :
        Except Error (Events.Observation Id Value Error)))
    (scanGroups_skip (projection schema) (predicate schema) source.readGroup before after group decoded rejected)

end Silmaril.Proofs.Formats.Parquet.Reader
