module

public import Silmaril.Semantics.Relational.Scan.Defs

public section

namespace Silmaril.Proofs.Relational.Scan

open Silmaril.Relational Silmaril.Relational.Scan

variable {Id Kind : Type*} {Value : Kind → Type*} {source : Schema Id Kind}

theorem scan_comp (p : Projection source) (q : Projection p.schema)
    (keepFirst : Predicate source Value) (keepSecond : Predicate p.schema Value)
    (rows : Table source Value) :
    (p.comp q).scan (fun row =>
      match keepFirst row with
      | some true => keepSecond (p.projectRow row)
      | result => result) rows =
    q.scan keepSecond (p.scan keepFirst rows) := by
  unfold Projection.scan Projection.project select
  rw [List.filter_map, List.filter_filter, List.map_map]
  apply congrArg (List.map (p.comp q).projectRow)
  apply List.filter_congr
  intro row _
  cases first : keepFirst row with
  | none => simp [Function.comp_def, first]
  | some keep => cases keep <;> simp [Function.comp_def, first]

end Silmaril.Proofs.Relational.Scan
