module

public import Silmaril.Courses.Cambridge.L1.Denotational
public import Silmaril.Semantics.ElgotMonads.Thms

/-! A compositional denotation of Cambridge L1 with state, stuck outcomes,
and partial iteration. The exception transformer preserves the store at a
stuck outcome. An undefined `Part` has no finite outcome. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.EffectfulDenotational

open Silmaril.Elgot

abbrev Computation := ExceptT Unit (StateT Store Part)

def run {α : Type} (m : Computation α) (s : Store) : Part (Except Unit α × Store) :=
  m.run.run s

def read (loc : Loc) : Computation Expr := ExceptT.mk fun s =>
  Part.some (match s.lookup loc with
    | some n => (.ok (.int n), s)
    | none => (.error (), s))

def write (loc : Loc) (n : Int) : Computation Expr := ExceptT.mk fun s =>
  Part.some (match s.update loc n with
    | some t => (.ok .skip, t)
    | none => (.error (), s))

def binary (op : Op) : Expr → Expr → Computation Expr
  | .int l, .int r => pure (Denotational.applyOp op l r)
  | _, _ => throw ()

def assign (loc : Loc) : Expr → Computation Expr
  | .int n => write loc n
  | _ => throw ()

def branch {α : Type} (yes no : Computation α) : Expr → Computation α
  | .bool true => yes
  | .bool false => no
  | _ => throw ()

def afterSkip {α : Type} (next : Computation α) : Expr → Computation α
  | .skip => next
  | _ => throw ()

/-- A false guard returns `skip`. A true guard runs the body and continues
with its updated store if the body returns `skip`. -/
def whileBody (test body : Computation Expr) : Unit → Computation (Expr ⊕ Unit) :=
  fun () => test >>= branch (body >>= afterSkip (pure (.inr ()))) (pure (.inl .skip))

/-- The structural interpretation uses Elgot iteration only at `loop`.
Both operands of a binary operator run before their shapes are checked. -/
noncomputable def denote : Expr → Computation Expr
  | .int n => pure (.int n)
  | .bool b => pure (.bool b)
  | .skip => pure .skip
  | .deref loc => read loc
  | .binary l op r => denote l >>= fun lv => denote r >>= binary op lv
  | .assign loc e => denote e >>= assign loc
  | .cond test yes no => denote test >>= branch (denote yes) (denote no)
  | .seq first second => denote first >>= afterSkip (denote second)
  | .loop test body => iter (whileBody (denote test) (denote body)) ()

@[simp] theorem run_pure {α : Type} (a : α) (s : Store) :
    run (pure a) s = Part.some (.ok a, s) := rfl

@[simp] theorem run_throw {α : Type} (s : Store) :
    run (throw () : Computation α) s = Part.some (.error (), s) := rfl

@[simp] theorem run_read (loc : Loc) (s : Store) :
    run (read loc) s = Part.some (match s.lookup loc with
      | some n => (.ok (.int n), s)
      | none => (.error (), s)) := rfl

@[simp] theorem run_write (loc : Loc) (n : Int) (s : Store) :
    run (write loc n) s = Part.some (match s.update loc n with
      | some t => (.ok .skip, t)
      | none => (.error (), s)) := rfl

theorem run_bind {α β : Type} (m : Computation α) (k : α → Computation β) (s : Store) :
    run (m >>= k) s = (run m s).bind fun (result, t) => match result with
      | .ok a => run (k a) t
      | .error error => Part.some (.error error, t) := by
  unfold run
  rw [_root_.ExceptT.run_bind, _root_.StateT.run_bind]
  congr 1
  funext entry
  obtain ⟨result, t⟩ := entry
  cases result <;> rfl

@[simp] theorem denote_value {v : Expr} (value : IsValue v) : denote v = pure v := by
  cases value <;> rfl

/-- The Elgot fixed-point law validates the original L1 unfolding rule. -/
theorem denote_loop_unfold (test body : Expr) :
    denote (.loop test body) = denote (.cond test (.seq body (.loop test body)) .skip) := by
  let again := iter (whileBody (denote test) (denote body))
  change again () = (denote test >>= branch (denote body >>= afterSkip (again ())) (pure .skip))
  have unfoldOnce := congrFun
    (LawfulElgotMonad.fixpoint (whileBody (denote test) (denote body))) ()
  refine unfoldOnce.trans ?_
  simp only [whileBody, bind_assoc]
  congr 1
  funext guard
  cases guard <;> simp [branch]
  case bool b =>
    cases b <;> simp [bind_assoc]
    congr 1
    funext value
    cases value <;> simp [afterSkip, again]

/-- Each direct reduction preserves the denotation when read at its store. -/
theorem step_preserves {source target : Config} (step : Step source target) :
    run (denote source.expr) source.store = run (denote target.expr) target.store := by
  induction step with
  | add | ge => simp [denote, binary]
  | binaryLeft _ ih =>
      simp only [denote, run_bind] at *
      rw [ih]
  | binaryRight value _ ih =>
      simp only [denote, denote_value value, pure_bind, run_bind] at *
      rw [ih]
  | deref present => simp [denote, present]
  | assignValue present =>
      simp [denote, assign, Store.update_eq_some _ _ _ present]
  | assignStep _ ih =>
      simp only [denote, run_bind] at *
      rw [ih]
  | seqSkip => simp [denote, afterSkip]
  | seqStep _ ih =>
      simp only [denote, run_bind] at *
      rw [ih]
  | ifTrue => simp [denote, branch]
  | ifFalse => simp [denote, branch]
  | ifStep _ ih =>
      simp only [denote, run_bind] at *
      rw [ih]
  | «while» => exact congrArg (fun m => run m _) (denote_loop_unfold _ _)

end Silmaril.Courses.Cambridge.L1.EffectfulDenotational
