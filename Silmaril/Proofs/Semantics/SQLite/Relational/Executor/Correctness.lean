module

public import Silmaril.Semantics.SQLite.Relational.Executor.Defs
public import Silmaril.Semantics.Relational.Query.Thms

public section

namespace Silmaril.Proofs.Semantics.SQLite.Relational.Executor

open Silmaril.SQLite.Relational

variable {p : Profile} {exec : Executor p} {ref : Reference p}

theorem sound (h : exec.Sound ref) : exec.denote.Sound ref.denote := by
  intro db call out observed
  change exec.execute db call = out at observed
  subst out
  change ref.Executes db call (exec.execute db call).1 (exec.execute db call).2
  cases resolved : exec.resolve db.catalog call.statement with
  | error error =>
    have step := Reference.Executes.prepareError (ref := ref) (call := call) (db := db)
      (h.resolve resolved)
    simpa [Executor.execute, Executor.prepare, resolved] using step
  | ok plan =>
    have admitted := h.resolve resolved
    cases binding : call.binding with
    | none =>
      have step := Reference.Executes.unbound admitted binding
      simpa [Executor.execute, Executor.prepare, resolved, binding, Executor.run] using step
    | some arg =>
      obtain ⟨index, key⟩ := arg
      by_cases range : index = 1
      · subst index
        have lookup : ref.reads (db.backing, db.cache) (plan.target, key)
            (exec.read (db.backing, db.cache) (plan.target, key)) := h.read rfl
        have step := Reference.Executes.seek admitted binding lookup
        simpa [Executor.execute, Executor.prepare, resolved, binding, Prepared.bindInt64,
          Executor.run] using step
      · have step := Reference.Executes.bindError admitted binding range
        simpa [Executor.execute, Executor.prepare, resolved, binding, Prepared.bindInt64,
          range] using step

theorem complete (h : exec.Complete ref) : exec.denote.Complete ref.denote := by
  intro db call out observed
  obtain ⟨result, after⟩ := out
  change ref.Executes db call result after at observed
  change exec.execute db call = (result, after)
  cases observed with
  | prepareError resolved =>
    simp [Executor.execute, Executor.prepare, show exec.resolve _ _ = _ from h.resolve resolved]
  | bindError resolved binding range =>
    simp [Executor.execute, Executor.prepare, show exec.resolve _ _ = _ from h.resolve resolved,
      binding, Prepared.bindInt64, range]
  | unbound resolved binding =>
    simp [Executor.execute, Executor.prepare, show exec.resolve _ _ = _ from h.resolve resolved,
      binding, Executor.run]
  | seek resolved binding lookup =>
    simp [Executor.execute, Executor.prepare, show exec.resolve _ _ = _ from h.resolve resolved,
      binding, Prepared.bindInt64, Executor.run, show exec.read _ _ = _ from h.read lookup]

theorem executeBatch_append (exec : Executor p) (db : Connection p)
    (first second : List (Invocation p.Ref)) :
    exec.executeBatch db (first ++ second) =
      (exec.executeBatch db first).andThen (fun after => exec.executeBatch after second) := by
  induction first generalizing db with
  | nil => rfl
  | cons call first ih =>
    simp only [List.cons_append, Executor.executeBatch]
    cases exec.execute db call with
    | mk result after =>
      cases result with
      | error error => rfl
      | ok result =>
        change (exec.executeBatch after (first ++ second)).prepend (result, after) =
          ((exec.executeBatch after first).prepend (result, after)).andThen
            (fun state => exec.executeBatch state second)
        rw [ih]
        generalize exec.executeBatch after first = out
        obtain ⟨⟨completed, failure⟩, state⟩ := out
        cases failure <;> rfl

theorem executeBatch_iff (sound : exec.Sound ref) (complete : exec.Complete ref)
    (db : Connection p) (calls : List (Invocation p.Ref)) (out : BatchOutcome p) :
    exec.executeBatch db calls = out ↔ ref.BatchExecutes db calls out := by
  constructor
  · intro eval
    induction calls generalizing db out with
    | nil =>
      subst out
      exact .nil db
    | cons call rest ih =>
      simp only [Executor.executeBatch] at eval
      cases head : exec.execute db call with
      | mk result after =>
        rw [head] at eval
        have step : ref.Executes db call result after :=
          Silmaril.Proofs.Semantics.SQLite.Relational.Executor.sound sound
            (db := db) (query := call) (result := (result, after)) head
        cases result with
        | error error =>
          subst out
          exact .stop step
        | ok result =>
          subst out
          exact .next step (ih after _ rfl)
  · intro runs
    induction runs with
    | nil => rfl
    | @stop db call rest error after head =>
      have eq : exec.execute db call = (.error error, after) :=
        Silmaril.Proofs.Semantics.SQLite.Relational.Executor.complete complete
          (result := (.error error, after)) head
      simp [Executor.executeBatch, eq]
    | @next db call rest result after out head _ ih =>
      have eq : exec.execute db call = (.ok result, after) :=
        Silmaril.Proofs.Semantics.SQLite.Relational.Executor.complete complete
          (result := (.ok result, after)) head
      simp [Executor.executeBatch, eq, ih]

theorem execute_connection (exec : Executor p) (db : Connection p)
    (call : Invocation p.Ref) :
    (exec.execute db call).2.catalog = db.catalog ∧ (exec.execute db call).2.session = db.session := by
  have run (stmt : Prepared p.Target) :
      (exec.run db stmt).2.catalog = db.catalog ∧ (exec.run db stmt).2.session = db.session := by
    obtain ⟨plan, key⟩ := stmt
    cases key <;> exact ⟨rfl, rfl⟩
  unfold Executor.execute
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact run _
    · split
      · exact ⟨rfl, rfl⟩
      · exact run _

theorem executeBatch_connection (exec : Executor p) (db : Connection p)
    (calls : List (Invocation p.Ref)) :
    (exec.executeBatch db calls).2.catalog = db.catalog ∧
      (exec.executeBatch db calls).2.session = db.session := by
  induction calls generalizing db with
  | nil => exact ⟨rfl, rfl⟩
  | cons call rest ih =>
    have head := execute_connection exec db call
    simp only [Executor.executeBatch]
    cases step : exec.execute db call with
    | mk reply after =>
      rw [step] at head
      cases reply with
      | error _ => exact head
      | ok _ =>
        obtain ⟨catalog, session⟩ := ih after
        exact ⟨catalog.trans head.1, session.trans head.2⟩

end Silmaril.Proofs.Semantics.SQLite.Relational.Executor
