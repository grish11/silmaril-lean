module

public import Silmaril.Semantics.Relational.Scan.Database.Defs
import Silmaril.Semantics.Relational.Database.Thms
import Silmaril.Proofs.Semantics.Relational.Scan.Laws

/-! Observation and scan laws for ordered nullable tables. -/

@[expose] public section

namespace Silmaril.Relational.Scan

variable {Name Id Kind : Type*} {Value : Kind → Type*} {source : Schema Id Kind}

@[simp] theorem Observation.ofColumns_ofRows (schema : Schema Id Kind) (rows : Table schema Value) :
    ofColumns schema (AlignedColumns.rowsEquiv rows) = ⟨schema, rows⟩ :=
  congrArg (Observation.mk schema) (AlignedColumns.rowsEquiv.symm_apply_apply rows)

@[simp] theorem Observation.rowCount_ofColumns (schema : Schema Id Kind)
    (columns : Columns schema Value) : (ofColumns schema columns).rowCount = columns.rowCount :=
  AlignedColumns.length_toRows columns

namespace Projection

@[simp] theorem project_id (rows : Table source Value) : (id source).project rows = rows :=
  List.map_id rows

theorem project_comp (p : Projection source) (q : Projection p.schema) (rows : Table source Value) :
    (p.comp q).project rows = q.project (p.project rows) :=
  (List.map_map (f := p.projectRow) (g := q.projectRow) (l := rows)).symm

/-- Projection preserves the row count, even with zero output columns. -/
@[simp] theorem length_project (p : Projection source) (rows : Table source Value) :
    (p.project rows).length = rows.length := List.length_map _

@[simp] theorem rowCount_projectColumns (p : Projection source) (columns : Columns source Value) :
    (p.projectColumns columns).rowCount = columns.rowCount := rfl

/-- Direct column projection and projection of the observed rows agree in
order, multiplicity, and all typed nullable cells. Their output schema is `p.schema`. -/
theorem rowsEquiv_projectColumns (p : Projection source) (columns : Columns source Value) :
    AlignedColumns.rowsEquiv.symm (p.projectColumns columns) =
      p.project (AlignedColumns.rowsEquiv.symm columns) :=
  Proofs.Relational.Scan.rowsEquiv_projectColumns p columns

theorem observe_projectColumns (p : Projection source) (columns : Columns source Value) :
    Observation.ofColumns p.schema (p.projectColumns columns) = ⟨p.schema, p.project columns.toRows⟩ :=
  congrArg (Observation.mk p.schema) (p.rowsEquiv_projectColumns columns)

@[simp] theorem scan_nil (p : Projection source) (predicate : Predicate source Value) :
    p.scan predicate [] = [] := rfl

theorem scan_append (p : Projection source) (predicate : Predicate source Value)
    (left right : Table source Value) :
    p.scan predicate (left ++ right) = p.scan predicate left ++ p.scan predicate right := by
  simp only [scan, select, project, List.filter_append, List.map_append]

@[simp] theorem length_scan (p : Projection source) (predicate : Predicate source Value)
    (rows : Table source Value) : (p.scan predicate rows).length = (select predicate rows).length :=
  length_project p _

/-- Selection can follow projection when the original predicate factors through
the selected row, including agreement on unknown. -/
theorem scan_eq_select_project (p : Projection source) (predicate : Predicate source Value)
    (projected : Predicate p.schema Value) (rows : Table source Value)
    (h : ∀ row, predicate row = projected (p.projectRow row)) :
    p.scan predicate rows = select projected (p.project rows) :=
  Proofs.Relational.Scan.scan_eq_select_project p predicate projected rows h

end Projection

@[simp] theorem observePacked_unpack
    (db : Database.Packed Name (fun s : Schema Id Kind => Table s Value)) :
    observeDependent (Database.Packed.unpack db) = observePacked db := by
  rw [observeDependent, Database.pack_unpack]

@[simp] theorem observeDependent_at_none
    (db : Database.Dependent Name (fun s : Schema Id Kind => Table s Value))
    (name : Name) (missing : db.fst name = none) : observeDependent db name = none := by
  apply (Database.erase_eq_none_iff Observation.mk db.pack name).2
  exact Option.map_eq_none_iff.mp ((congrFun (Database.catalog_pack db) name).trans missing)

theorem observeDependent_at_some
    (db : Database.Dependent Name (fun s : Schema Id Kind => Table s Value))
    (name : Name) {schema : Schema Id Kind} (found : db.fst name = some schema) :
    observeDependent db name = some ⟨schema, db.snd.lookup name found⟩ :=
  Proofs.Relational.Scan.observeDependent_at_some db name found

end Silmaril.Relational.Scan
