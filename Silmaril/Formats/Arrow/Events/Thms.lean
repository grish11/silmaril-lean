module

public import Silmaril.Formats.Arrow.Events.Defs
import Silmaril.Proofs.Formats.Arrow.Events
import Silmaril.Semantics.Relational.Scan.Thms

/-! Observational equivalence and logical scan laws for abstract Arrow events. -/

public section

namespace Silmaril.Formats.Arrow.Events

open Silmaril.Relational

variable {Id Kind Error : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

namespace Trace

/-- Batch-wise scanning observes exactly the scan of the flattened ordered input. -/
theorem rows_scan (trace : Trace schema Value Error) (projection : Scan.Projection schema)
    (predicate : Scan.Predicate schema Value) :
    (trace.scan projection predicate).rows = projection.scan predicate trace.rows :=
  Proofs.Formats.Arrow.Events.rows_scan trace projection predicate

@[simp] theorem termination_scan (trace : Trace schema Value Error)
    (projection : Scan.Projection schema) (predicate : Scan.Predicate schema Value) :
    (trace.scan projection predicate).termination = trace.termination := rfl

/-- One output row position per kept row, including projections to width zero. -/
theorem rowCount_scan (trace : Trace schema Value Error) (projection : Scan.Projection schema)
    (predicate : Scan.Predicate schema Value) :
    (trace.scan projection predicate).collect.table.rowCount = (Scan.select predicate trace.rows).length :=
  (congrArg List.length (trace.rows_scan projection predicate)).trans (projection.length_scan predicate _)

end Trace

namespace EventStream

theorem equivalent_equivalence : Equivalence (Equivalent (Id := Id) (Value := Value) (Error := Error)) :=
  ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem equivalent_open_schema {other : Scan.Schema Id Kind}
    {left : Trace schema Value Error} {right : Trace other Value Error}
    (equal : Equivalent (.ok ⟨schema, left⟩) (.ok ⟨other, right⟩)) : schema = other :=
  congrArg (fun observation : Observation Id Value Error => observation.table.schema)
    (Except.ok.inj equal)

theorem equivalent_open_iff {left right : Trace schema Value Error} :
    Equivalent (.ok ⟨schema, left⟩) (.ok ⟨schema, right⟩) ↔
      left.rows = right.rows ∧ left.termination = right.termination :=
  Proofs.Formats.Arrow.Events.equivalent_open_iff

theorem equivalent_insert_empty (trace : Trace schema Value Error)
    (before after : List (Batch schema Value)) (batch : Batch schema Value)
    (split : trace.batches = before ++ after) (empty : batch.rowCount = 0) :
    Equivalent (.ok ⟨schema, ⟨before ++ batch :: after, trace.termination⟩⟩) (.ok ⟨schema, trace⟩) :=
  equivalent_open_iff.mpr
    ⟨Proofs.Formats.Arrow.Events.rows_insert_empty trace before after batch split empty, rfl⟩

/-- Collection and schema-dependent logical scanning commute, preserving the
distinction between open errors and terminal outcomes of an opened reader. -/
theorem collect_scan (stream : EventStream Id Value Error)
    (projection : (schema : Scan.Schema Id Kind) → Scan.Projection schema)
    (predicate : (schema : Scan.Schema Id Kind) → Scan.Predicate schema Value) :
    (stream.scan projection predicate).collect = stream.collect.map (fun observation =>
      let schema := observation.table.schema
      ⟨⟨(projection schema).schema, (projection schema).scan (predicate schema) observation.table.rows⟩,
        observation.termination⟩) :=
  Proofs.Formats.Arrow.Events.collect_scan stream projection predicate

theorem Equivalent.scan {left right : EventStream Id Value Error} (equal : Equivalent left right)
    (projection : (schema : Scan.Schema Id Kind) → Scan.Projection schema)
    (predicate : (schema : Scan.Schema Id Kind) → Scan.Predicate schema Value) :
    Equivalent (left.scan projection predicate) (right.scan projection predicate) := by
  unfold Equivalent at *
  rw [collect_scan, collect_scan, equal]

/-- Rebatching a completed trace preserves logical scans when the flattened
rows and terminal outcome agree. -/
theorem scan_rechunk {left right : Trace schema Value Error} (projection : Scan.Projection schema)
    (predicate : Scan.Predicate schema Value) (rows : left.rows = right.rows)
    (termination : left.termination = right.termination) :
    Equivalent (.ok ⟨projection.schema, left.scan projection predicate⟩)
      (.ok ⟨projection.schema, right.scan projection predicate⟩) :=
  equivalent_open_iff.mpr ⟨by rw [Trace.rows_scan, Trace.rows_scan, rows], termination⟩

end EventStream

end Silmaril.Formats.Arrow.Events
