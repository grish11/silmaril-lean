module

public import Silmaril.Semantics.SQLite.Relational.Executor.Defs
public import Silmaril.Semantics.Relational.Query.Thms
import Silmaril.Proofs.Semantics.SQLite.Relational.Executor.Correctness

public section

namespace Silmaril.SQLite.Relational.Executor

open Silmaril.Relational (QueryRel)

variable {p : Profile} {exec : Executor p} {ref : Reference p}

/-- Pointwise soundness of the dependencies extends to the full poststate. -/
theorem sound (h : exec.Sound ref) : exec.denote.Sound ref.denote :=
  Proofs.Semantics.SQLite.Relational.Executor.sound h

theorem complete (h : exec.Complete ref) : exec.denote.Complete ref.denote :=
  Proofs.Semantics.SQLite.Relational.Executor.complete h

theorem refines (h : exec.Sound ref) : exec.denote.Refines ref.denote := sound h

theorem equivalent (hs : exec.Sound ref) (hc : exec.Complete ref) :
    exec.denote.Equivalent ref.denote :=
  fun {_ _} _ _ => ⟨sound hs, complete hc⟩

theorem deterministic (exec : Executor p) : exec.denote.Deterministic :=
  QueryRel.ofTotal_deterministic exec.execute

theorem total (exec : Executor p) : exec.denote.Total :=
  QueryRel.ofTotal_total exec.execute

theorem reference_deterministic (h : exec.Complete ref) : ref.denote.Deterministic :=
  QueryRel.Refines.deterministic (impl := ref.denote) (spec := exec.denote)
    (complete h) (deterministic exec)

theorem reference_total (h : exec.Sound ref) : ref.denote.Total :=
  QueryRel.Refines.total (impl := exec.denote) (spec := ref.denote) (sound h) (total exec)

/-- Both the admitted and the rejected run paths preserve read-only session fields. -/
theorem run_session (exec : Executor p) (db : Connection p) (stmt : Prepared p.Target) :
    (exec.run db stmt).2.session = db.session := by
  obtain ⟨plan, key⟩ := stmt
  cases key <;> rfl

theorem executeBatch_append (exec : Executor p) (db : Connection p)
    (first second : List (Invocation p.Ref)) :
    exec.executeBatch db (first ++ second) =
      (exec.executeBatch db first).andThen (fun after => exec.executeBatch after second) :=
  Proofs.Semantics.SQLite.Relational.Executor.executeBatch_append exec db first second

theorem executeBatch_iff (hs : exec.Sound ref) (hc : exec.Complete ref)
    (db : Connection p) (calls : List (Invocation p.Ref)) (out : BatchOutcome p) :
    exec.executeBatch db calls = out ↔ ref.BatchExecutes db calls out :=
  Proofs.Semantics.SQLite.Relational.Executor.executeBatch_iff hs hc db calls out

/-- A read-only invocation preserves the logical catalog and session fields. -/
theorem execute_connection (exec : Executor p) (db : Connection p) (call : Invocation p.Ref) :
    (exec.execute db call).2.catalog = db.catalog ∧ (exec.execute db call).2.session = db.session :=
  Proofs.Semantics.SQLite.Relational.Executor.execute_connection exec db call

theorem executeBatch_connection (exec : Executor p) (db : Connection p)
    (calls : List (Invocation p.Ref)) :
    (exec.executeBatch db calls).2.catalog = db.catalog ∧
      (exec.executeBatch db calls).2.session = db.session :=
  Proofs.Semantics.SQLite.Relational.Executor.executeBatch_connection exec db calls

end Silmaril.SQLite.Relational.Executor
