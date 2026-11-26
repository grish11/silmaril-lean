module

public import Silmaril.Semantics.Relational.Scan.Defs
import Silmaril.Proofs.Semantics.Relational.Scan.Composition

public section

namespace Silmaril.Relational.Scan.Projection

open Silmaril.Relational.Scan

variable {Id Kind : Type*} {Value : Kind → Type*} {source : Schema Id Kind}

/-- Compose row scans in input order. The second predicate sees the first
projected row only when the first predicate is true. False and unknown
from the first predicate both discard the row. -/
theorem scan_comp (p : Projection source) (q : Projection p.schema)
    (keepFirst : Predicate source Value) (keepSecond : Predicate p.schema Value)
    (rows : Table source Value) :
    (p.comp q).scan (fun row =>
      match keepFirst row with
      | some true => keepSecond (p.projectRow row)
      | result => result) rows =
    q.scan keepSecond (p.scan keepFirst rows) :=
  Proofs.Relational.Scan.scan_comp p q keepFirst keepSecond rows

end Silmaril.Relational.Scan.Projection
