module

public import Silmaril.Formats.Arrow.Events.Defs
import Silmaril.Proofs.Formats.Arrow.Events.Composition

public section

namespace Silmaril.Formats.Arrow.Events.EventStream

open Silmaril.Relational

variable {Id Kind Error : Type*} {Value : Kind → Type*}

/-- Two logical scans have the same observed rows, schema and outcome
as one composed scan. This applies to open errors and partial traces. -/
theorem scan_comp (stream : EventStream Id Value Error)
    (p q : (schema : Scan.Schema Id Kind) → Scan.Projection schema)
    (keepFirst keepSecond : (schema : Scan.Schema Id Kind) → Scan.Predicate schema Value) :
    Equivalent
      (stream.scan (fun schema => (p schema).comp (q (p schema).schema)) (fun schema row =>
        match keepFirst schema row with
        | some true => keepSecond (p schema).schema ((p schema).projectRow row)
        | result => result))
      ((stream.scan p keepFirst).scan q keepSecond) :=
  Proofs.Formats.Arrow.Events.scan_comp stream p q keepFirst keepSecond

end Silmaril.Formats.Arrow.Events.EventStream
