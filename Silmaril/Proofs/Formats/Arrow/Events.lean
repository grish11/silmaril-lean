module

public import Silmaril.Formats.Arrow.Events.Defs
import Silmaril.Semantics.Relational.Scan.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.Events

open Silmaril.Formats.Arrow.Events Silmaril.Relational

variable {Id Kind Error : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

theorem rows_scan (trace : Trace schema Value Error) (projection : Scan.Projection schema)
    (predicate : Scan.Predicate schema Value) :
    (trace.scan projection predicate).rows = projection.scan predicate trace.rows := by
  have flatten (batches : List (Batch schema Value)) :
      List.flatMap AlignedColumns.toRows
          (batches.map (fun batch => AlignedColumns.ofRows (projection.scan predicate batch.toRows))) =
        projection.scan predicate (batches.flatMap AlignedColumns.toRows) := by
    induction batches with
    | nil => rfl
    | cons batch rest ih =>
      simp only [List.map_cons, List.flatMap_cons, AlignedColumns.toRows_ofRows, ih,
        Scan.Projection.scan_append]
  exact flatten trace.batches

theorem rows_insert_empty (trace : Trace schema Value Error)
    (before after : List (Batch schema Value)) (batch : Batch schema Value)
    (split : trace.batches = before ++ after) (empty : batch.rowCount = 0) :
    (⟨before ++ batch :: after, trace.termination⟩ : Trace schema Value Error).rows = trace.rows := by
  have emptyRows : batch.toRows = [] :=
    List.length_eq_zero_iff.mp ((AlignedColumns.length_toRows batch).trans empty)
  simp only [Trace.rows, split, List.flatMap_append, List.flatMap_cons, emptyRows, List.nil_append]

theorem equivalent_open_iff {left right : Trace schema Value Error} :
    EventStream.Equivalent (.ok ⟨schema, left⟩) (.ok ⟨schema, right⟩) ↔
      left.rows = right.rows ∧ left.termination = right.termination := by
  constructor
  · intro equal
    have observation : left.collect = right.collect := Except.ok.inj equal
    have table : (⟨schema, left.rows⟩ : Scan.Observation Id Value) = ⟨schema, right.rows⟩ :=
      congrArg Observation.table observation
    exact ⟨eq_of_heq (Scan.Observation.mk.inj table).2, congrArg Observation.termination observation⟩
  · rintro ⟨rows, termination⟩
    change Except.ok left.collect = Except.ok right.collect
    simp only [Trace.collect, rows, termination]

theorem collect_scan (stream : EventStream Id Value Error)
    (projection : (schema : Scan.Schema Id Kind) → Scan.Projection schema)
    (predicate : (schema : Scan.Schema Id Kind) → Scan.Predicate schema Value) :
    (stream.scan projection predicate).collect = stream.collect.map (fun observation =>
      let schema := observation.table.schema
      ⟨⟨(projection schema).schema, (projection schema).scan (predicate schema) observation.table.rows⟩,
        observation.termination⟩) := by
  rcases stream with error | ⟨schema, trace⟩
  · rfl
  · exact congrArg
      (fun rows => Except.ok (⟨⟨(projection schema).schema, rows⟩, trace.termination⟩ :
        Observation Id Value Error))
      (rows_scan trace (projection schema) (predicate schema))

end Silmaril.Proofs.Formats.Arrow.Events
