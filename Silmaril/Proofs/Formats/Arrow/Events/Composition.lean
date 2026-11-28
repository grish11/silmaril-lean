module

public import Silmaril.Formats.Arrow.Events.Defs
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Semantics.Relational.Scan.Composition.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.Events

open Silmaril.Relational Silmaril.Formats.Arrow.Events

variable {Id Kind Error : Type*} {Value : Kind → Type*}

theorem scan_comp (stream : EventStream Id Value Error)
    (p q : (schema : Scan.Schema Id Kind) → Scan.Projection schema)
    (keepFirst keepSecond : (schema : Scan.Schema Id Kind) → Scan.Predicate schema Value) :
    EventStream.Equivalent
      (stream.scan (fun schema => (p schema).comp (q (p schema).schema)) (fun schema row =>
        match keepFirst schema row with
        | some true => keepSecond (p schema).schema ((p schema).projectRow row)
        | result => result))
      ((stream.scan p keepFirst).scan q keepSecond) := by
  unfold EventStream.Equivalent
  rw [EventStream.collect_scan, EventStream.collect_scan, EventStream.collect_scan]
  cases stream.collect with
  | error reason => rfl
  | ok observation =>
    rcases observation with ⟨⟨schema, rows⟩, termination⟩
    simp only [Except.map]
    let projected := (p schema).schema
    exact congrArg
      (fun rows : Scan.Table (q projected).schema Value =>
        (Except.ok ⟨⟨(q projected).schema, rows⟩, termination⟩ : Except Error (Observation Id Value Error)))
      ((p schema).scan_comp (q projected) (keepFirst schema) (keepSecond projected) rows)

end Silmaril.Proofs.Formats.Arrow.Events
