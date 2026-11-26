module

public import Silmaril.Semantics.Relational.Scan.Database.Defs

public section

namespace Silmaril.Proofs.Relational.Scan

open Silmaril.Relational
open Silmaril.Relational.Scan

variable {Name Id Kind : Type*} {Value : Kind → Type*} {source : Schema Id Kind}

theorem rowsEquiv_projectColumns (p : Projection source) (columns : Columns source Value) :
    AlignedColumns.rowsEquiv.symm (p.projectColumns columns) =
      p.project (AlignedColumns.rowsEquiv.symm columns) := by
  change (p.projectColumns columns).toRows = p.project columns.toRows
  unfold AlignedColumns.toRows Projection.project
  rw [List.map_ofFn]
  rfl

theorem scan_eq_select_project (p : Projection source) (predicate : Predicate source Value)
    (projected : Predicate p.schema Value) (rows : Table source Value)
    (h : ∀ row, predicate row = projected (p.projectRow row)) :
    p.scan predicate rows = select projected (p.project rows) := by
  unfold Projection.scan Projection.project select
  rw [List.filter_map]
  simp only [Function.comp_def, h]
  rfl

theorem observeDependent_at_some
    (db : Database.Dependent Name (fun s : Schema Id Kind => Table s Value))
    (name : Name) {schema : Schema Id Kind} (found : db.fst name = some schema) :
    observeDependent db name = some ⟨schema, db.snd.lookup name found⟩ := by
  have packFound (entry : Option (Schema Id Kind))
      (payload : Database.Payload (fun s => Scan.Table s Value) entry) (h : entry = some schema) :
      Database.packEntry entry payload =
        some ⟨schema, cast (congrArg (Database.Payload (fun s => Scan.Table s Value)) h) payload⟩ := by
    cases h
    rfl
  exact congrArg (Option.map fun entry => Observation.mk entry.fst entry.snd)
    (packFound (db.fst name) (db.snd name) found)

end Silmaril.Proofs.Relational.Scan
