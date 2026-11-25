module

public import Silmaril.Courses.Cambridge.L1.Reduction
public import Cslib.Foundations.Relation.Termination

/-! # Denotations for read-only L1 expressions

The denotation is a structural function of the expression and a fixed L1
store. Failure on this fragment means that reduction reaches a stuck term.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.Denotational

/-- The fragment contains literals, `skip`, reads, integer operators, and
conditionals. It admits ill-shaped operands and reads from partial stores. -/
inductive ReadOnly : Expr → Prop where
  | int (n : Int) : ReadOnly (.int n)
  | bool (b : Bool) : ReadOnly (.bool b)
  | skip : ReadOnly .skip
  | deref (loc : Loc) : ReadOnly (.deref loc)
  | binary {l r : Expr} {op : Op} : ReadOnly l → ReadOnly r → ReadOnly (.binary l op r)
  | cond {test yes no : Expr} : ReadOnly test → ReadOnly yes → ReadOnly no →
      ReadOnly (.cond test yes no)

/-- Extract the integer payload of an integer value. -/
@[simp] def asInt : Expr → Option Int
  | .int n => some n
  | _ => none

/-- Extract the Boolean payload of a Boolean value. -/
@[simp] def asBool : Expr → Option Bool
  | .bool b => some b
  | _ => none

/-- Interpret an L1 operator on integer operands. -/
@[simp] def applyOp (op : Op) (l r : Int) : Expr :=
  match op with
  | .add => .int (l + r)
  | .ge => .bool (l ≥ r)

/-- Read operands from the same store and interpret operators on values.
Conditionals use only the branch selected by the guard. Theorems about this
function require `ReadOnly` at the source. -/
def denote : Expr → Store → Option Expr
  | .int n, _ => some (.int n)
  | .bool b, _ => some (.bool b)
  | .skip, _ => some .skip
  | .deref loc, s => (s.lookup loc).map Expr.int
  | .binary l op r, s =>
      ((denote l s).bind asInt).bind fun lv =>
        ((denote r s).bind asInt).bind fun rv => some (applyOp op lv rv)
  | .cond test yes no, s =>
      ((denote test s).bind asBool).bind fun b =>
        if b then denote yes s else denote no s
  | .assign .., _ | .seq .., _ | .loop .., _ => none

private def weight : Expr → Nat
  | .deref _ => 1
  | .binary l _ r => weight l + weight r + 1
  | .cond test yes no => weight test + weight yes + weight no + 1
  | _ => 0

private theorem step_invariant {source target : Config} (step : Step source target)
    (fragment : ReadOnly source.expr) :
    ReadOnly target.expr ∧ target.store = source.store ∧
      denote target.expr target.store = denote source.expr source.store ∧
      weight target.expr < weight source.expr := by
  induction step with
  | add => exact ⟨.int _, rfl, rfl, by simp [weight]⟩
  | ge => exact ⟨.bool _, rfl, rfl, by simp [weight]⟩
  | @binaryLeft l l' r op s s' _ ih =>
      cases fragment with
      | binary left right =>
          obtain ⟨left', store, same, smaller⟩ := ih left
          change s' = s at store
          subst s'
          change denote l' s = denote l s at same
          change weight l' < weight l at smaller
          exact ⟨.binary left' right, rfl, by simp [denote, same], by simp only [weight]; omega⟩
  | @binaryRight l r r' op s s' _ _ ih =>
      cases fragment with
      | binary left right =>
          obtain ⟨right', store, same, smaller⟩ := ih right
          change s' = s at store
          subst s'
          change denote r' s = denote r s at same
          change weight r' < weight r at smaller
          exact ⟨.binary left right', rfl, by simp [denote, same], by simp only [weight]; omega⟩
  | deref present =>
      exact ⟨.int _, rfl, by simp [denote, present], by simp [weight]⟩
  | ifTrue =>
      cases fragment with
      | cond _ yes _ => exact ⟨yes, rfl, rfl, by simp only [weight]; omega⟩
  | ifFalse =>
      cases fragment with
      | cond _ _ no => exact ⟨no, rfl, rfl, by simp only [weight]; omega⟩
  | @ifStep test test' yes no s s' _ ih =>
      cases fragment with
      | cond guard left right =>
          obtain ⟨guard', store, same, smaller⟩ := ih guard
          change s' = s at store
          subst s'
          change denote test' s = denote test s at same
          change weight test' < weight test at smaller
          exact ⟨.cond guard' left right, rfl, by simp [denote, same], by simp only [weight]; omega⟩
  | assignValue | assignStep | seqSkip | seqStep | «while» => cases fragment

private theorem steps_invariant {source target : Config} (path : Steps source target)
    (fragment : ReadOnly source.expr) : ReadOnly target.expr ∧ target.store = source.store ∧
      denote target.expr target.store = denote source.expr source.store := by
  induction path with
  | refl => exact ⟨fragment, rfl, rfl⟩
  | tail _ step ih =>
      obtain ⟨fragment', store, same, _⟩ := step_invariant step ih.1
      exact ⟨fragment', store.trans ih.2.1, same.trans ih.2.2⟩

private theorem asInt_eq_some {v : Expr} {n : Int} : asInt v = some n ↔ v = .int n := by
  cases v <;> simp [asInt]

private theorem asBool_eq_some {v : Expr} {b : Bool} : asBool v = some b ↔ v = .bool b := by
  cases v <;> simp [asBool]

private theorem steps_of_denote {e v : Expr} {s : Store} (fragment : ReadOnly e)
    (result : denote e s = some v) : Steps ⟨e, s⟩ ⟨v, s⟩ ∧ IsValue v := by
  induction fragment generalizing v with
  | int n =>
      cases result
      exact ⟨.refl, .int n⟩
  | bool b =>
      cases result
      exact ⟨.refl, .bool b⟩
  | skip =>
      cases result
      exact ⟨.refl, .skip⟩
  | deref loc =>
      change (s.lookup loc).map Expr.int = some v at result
      obtain ⟨n, lookup, rfl⟩ := Option.map_eq_some_iff.mp result
      exact ⟨.single (.deref lookup), .int n⟩
  | @binary l r op left right ihLeft ihRight =>
      simp only [denote, Option.bind_eq_some_iff, asInt_eq_some, Option.some.injEq] at result
      obtain ⟨lv, ⟨_, leftResult, rfl⟩, rv, ⟨_, rightResult, rfl⟩, rfl⟩ := result
      have toLeft := Relation.ReflTransGen.lift
        (fun c : Config => (⟨.binary c.expr op r, c.store⟩ : Config))
        (fun ⟨_, _⟩ ⟨_, _⟩ step => Step.binaryLeft step) _ _ (ihLeft leftResult).1
      have toRight := Relation.ReflTransGen.lift
        (fun c : Config => (⟨.binary (.int lv) op c.expr, c.store⟩ : Config))
        (fun ⟨_, _⟩ ⟨_, _⟩ step => Step.binaryRight (.int lv) step) _ _ (ihRight rightResult).1
      cases op with
      | add => exact ⟨(toLeft.trans toRight).tail (.add lv rv s), .int _⟩
      | ge => exact ⟨(toLeft.trans toRight).tail (.ge lv rv s), .bool _⟩
  | @cond test yes no guard left right ihGuard ihYes ihNo =>
      simp only [denote, Option.bind_eq_some_iff, asBool_eq_some] at result
      obtain ⟨b, ⟨_, guardResult, rfl⟩, branchResult⟩ := result
      have toGuard := Relation.ReflTransGen.lift
        (fun c : Config => (⟨.cond c.expr yes no, c.store⟩ : Config))
        (fun ⟨_, _⟩ ⟨_, _⟩ step => Step.ifStep step) _ _ (ihGuard guardResult).1
      cases b with
      | false =>
          obtain ⟨path, value⟩ := ihNo branchResult
          exact ⟨(toGuard.tail .ifFalse).trans path, value⟩
      | true =>
          obtain ⟨path, value⟩ := ihYes branchResult
          exact ⟨(toGuard.tail .ifTrue).trans path, value⟩

private theorem denote_value {e : Expr} (value : IsValue e) (s : Store) :
    denote e s = some e := by
  cases value <;> rfl

/-- A successful denotation agrees exactly with finite reduction to a value
in the full L1 configuration, including its unchanged store. -/
theorem denote_eq_some_iff {source target : Config} (fragment : ReadOnly source.expr) :
    (denote source.expr source.store = some target.expr ∧ target.store = source.store) ↔
      Steps source target ∧ IsValue target.expr := by
  constructor
  · rcases source with ⟨e, s⟩
    rcases target with ⟨v, t⟩
    rintro ⟨result, store⟩
    cases store
    exact steps_of_denote fragment result
  · rintro ⟨path, value⟩
    obtain ⟨_, store, same⟩ := steps_invariant path fragment
    exact ⟨same.symm.trans (denote_value value _), store⟩

/-- Every read-only source is strongly normalizing in the original relation. -/
theorem stronglyNormal (source : Config) (fragment : ReadOnly source.expr) :
    Relation.SN Step source := by
  apply Relation.SN.intro
  intro next step
  exact stronglyNormal next (step_invariant step fragment).1
termination_by weight source.expr
decreasing_by exact (step_invariant step fragment).2.2.2

/-- Failure on the fragment is exactly finite reachability of a stuck term. -/
theorem denote_eq_none_iff {source : Config} (fragment : ReadOnly source.expr) :
    denote source.expr source.store = none ↔ ∃ target, Steps source target ∧ Stuck target := by
  constructor
  · intro failed
    obtain ⟨target, path, normal⟩ := (stronglyNormal source fragment).normalizable
    refine ⟨target, path, ?_, (Relation.normal_iff _ _).mp normal⟩
    intro value
    have result := ((denote_eq_some_iff fragment).2 ⟨path, value⟩).1
    rw [failed] at result
    cases result
  · rintro ⟨target, path, stuck⟩
    cases outcome : denote source.expr source.store with
    | none => rfl
    | some v =>
        obtain ⟨fragment', _, same⟩ := steps_invariant path fragment
        obtain ⟨run, value⟩ := steps_of_denote fragment' (same.trans outcome)
        have equal := (Relation.reflTransGen_iff_eq stuck.2).mp run
        exact (stuck.1 (equal ▸ value)).elim

end Silmaril.Courses.Cambridge.L1.Denotational
