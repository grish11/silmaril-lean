module

public import Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Defs
public import Silmaril.Semantics.SQLite.Relational.Fragment.Thms

public section

namespace Silmaril.Proofs.Semantics.SQLite.Relational.Executor.Catalog

open Silmaril.SQLite.Relational
open Silmaril.SQLite.Relational.CatalogExecutor
open Silmaril.Relational (QueryRel)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

theorem lookup_iff (target : Target sem) (key : Int64) (cell : Option SqlValue) :
    target.lookup key = cell ↔ target.Matches key cell := by
  obtain ⟨schema, column, table⟩ := target
  have valid := table.property.2
  unfold Target.lookup Target.Matches
  simp only [CheckedTable.rows]
  generalize table.val = rows at valid ⊢
  induction rows with
  | nil => cases cell <;> simp
  | cons first rest ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp valid
    by_cases found : TableRow.rowId? first = some key
    · have absent : ∀ row ∈ rest, TableRow.rowId? row ≠ some key := by
        intro row inside same
        have distinct := head row inside
        simp [TableSchema.distinctRows, found, same] at distinct
      cases cell with
      | none =>
        simp [List.find?, found]
      | some value =>
        have hit : (TableRow.rowId? first == some key) = true := by simp [found]
        simp only [List.find?, hit, Option.map_some, Option.some.injEq]
        constructor
        · intro valueEq
          exact ⟨first, List.mem_cons_self, found, valueEq⟩
        · rintro ⟨row, inside, same, valueEq⟩
          rcases List.mem_cons.mp inside with rfl | inTail
          · exact valueEq
          · exact False.elim (absent row inTail same)
    · have miss : (TableRow.rowId? first == some key) = false := by
        cases eq : (TableRow.rowId? first == some key)
        · rfl
        · exact False.elim (found (eq_of_beq eq))
      simp only [List.find?, miss]
      refine (ih tail).trans ?_
      cases cell with
      | none =>
        constructor
        · intro restAbsent row inside
          rcases List.mem_cons.mp inside with rfl | inTail
          · exact found
          · exact restAbsent row inTail
        · intro allAbsent row inside
          exact allAbsent row (List.mem_cons_of_mem first inside)
      | some value =>
        constructor
        · rintro ⟨row, inside, same, valueEq⟩
          exact ⟨row, List.mem_cons_of_mem first inside, same, valueEq⟩
        · rintro ⟨row, inside, same, valueEq⟩
          rcases List.mem_cons.mp inside with rfl | inTail
          · exact False.elim (found same)
          · exact ⟨row, inTail, same, valueEq⟩

theorem executor_sound (sem : TableSemantics SqlValue Affinity Expr) :
    (executor sem).Sound (reference sem) := by
  refine ⟨fun h => h, ?_⟩
  intro _ query out evaluated
  exact ⟨query.1.lookup query.2, (lookup_iff _ _ _).mp rfl, evaluated⟩

theorem executor_complete (sem : TableSemantics SqlValue Affinity Expr) :
    (executor sem).Complete (reference sem) := by
  refine ⟨fun h => h, ?_⟩
  intro _ query out observed
  obtain ⟨cell, seen, eq⟩ := observed
  change readOutcome (query.1.lookup query.2) = out
  rw [(lookup_iff _ _ _).mpr seen, eq]

theorem execute_eq (sem : TableSemantics SqlValue Affinity Expr) :
    QueryRel.ofTotal (execute sem) = CatalogExecutor.denote sem := by
  have eq : (executor sem).denote = (reference sem).denote :=
    (QueryRel.equivalent_iff_eq (impl := (executor sem).denote) (spec := (reference sem).denote)).mp
      (Executor.equivalent (executor_sound sem) (executor_complete sem))
  funext db call out
  change QueryRel.ofTotal (executor sem).check db (classify db.catalog call) out =
    CheckedRequest.denote (reference sem).denote db (classify db.catalog call) out
  rw [Executor.check_eq, eq]

end Silmaril.Proofs.Semantics.SQLite.Relational.Executor.Catalog
