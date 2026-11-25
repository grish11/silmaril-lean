module

public import Silmaril.Courses.Cambridge.L3
import Silmaril.Courses.Cambridge.L3.Interpreter
meta import Silmaril.Courses.Cambridge.L3.Interpreter
meta import Silmaril.Courses.Cambridge.L3.Store
meta import Silmaril.Courses.Cambridge.L3.Syntax

/-! # Checked L3 derivations for sums, records and references -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Examples

def increment : Expr :=
  .lam .int (.binary (.bvar 0) .add (.int 1))

def identityValue : Value :=
  ⟨.lam .int (.bvar 0), .lam _ _⟩

def incrementValue : Value :=
  ⟨increment, .lam _ _⟩

/-- Allocate a function cell, replace its contents, then call through it. -/
def functionCell : Expr :=
  .letE (.ref (.arr .int .int)) (.ref identityValue.val)
    (.seq (.assign (.bvar 0) increment) (.app (.deref (.bvar 0)) (.int 7)))

def functionStore : Store :=
  (∅ : Store).insert 0 incrementValue

theorem functionCell_typed : HasType ∅ .empty functionCell .int :=
  .letE (.ref (.lam (.bvar rfl))) (.seq
    (.assign (.bvar rfl) (.lam (.add (.bvar rfl) (.int 1))))
    (.app (.deref (.bvar rfl)) (.int 7)))

theorem functionCell_trace : Steps ⟨functionCell, ∅⟩ ⟨.int 8, functionStore⟩ := by
  have allocate : Step ⟨.ref identityValue.val, ∅⟩
      ⟨.loc 0, (∅ : Store).insert 0 identityValue⟩ :=
    .refValue identityValue Finmap.notMem_empty
  refine .head (.letStep allocate) (.head (.letValue (.loc 0)) ?_)
  have assign : Step ⟨.assign (.loc 0) increment, (∅ : Store).insert 0 identityValue⟩
      ⟨.skip, functionStore⟩ := by
    change Step ⟨.assign (.loc 0) incrementValue.val, _⟩ _
    simpa only [functionStore, Finmap.insert_insert] using
      Step.assignValue incrementValue (s := (∅ : Store).insert 0 identityValue) (loc := 0) (by simp)
  refine .head (.seqStep assign) (.head .seqSkip ?_)
  refine .head (.appLeft (.derefValue (value := incrementValue) (by simp [functionStore]))) ?_
  exact .head (.appFun (.int 7)) (.single (.add 7 1 _))

def intOrBool : Ty := .sum .int .bool

def sumProgram : Expr :=
  .matchSum (.inr (.bool true) intOrBool) .int (.bvar 0) .bool
    (.cond (.bvar 0) (.fst (.pair (.int 5) (.bool false))) (.int 0))

theorem sumProgram_typed : HasType ∅ .empty sumProgram .int :=
  .matchSum (.inr (.bool true)) (.bvar rfl)
    (.cond (.bvar rfl) (.fst (.pair (.int 5) (.bool false))) (.int 0))

theorem sumProgram_trace : Steps ⟨sumProgram, ∅⟩ ⟨.int 5, ∅⟩ :=
  .head (.matchRight (.bool true)) (.head .ifTrue (.single (.fstValue (.int 5) (.bool false))))

example : (Expr.lam .bool (.pair (.bvar 1) (.bvar 0))).beta (.bvar 0) =
    .lam .bool (.pair (.bvar 1) (.bvar 0)) := rfl

abbrev recordLabels : RecordLabels :=
  ⟨["first", "second"], by decide⟩

def zero : Value := ⟨.int 0, .int 0⟩
def one : Value := ⟨.int 1, .int 1⟩
def two : Value := ⟨.int 2, .int 2⟩

def writes (i : recordLabels.Index) : Expr :=
  if i = 0 then .assign (.loc 0) one.val else .assign (.loc 0) two.val

/-- Even a projection of the first field evaluates the second field's effect. -/
def recordProgram : Expr :=
  .project (.record recordLabels writes) "first"

theorem recordProgram_typed :
    HasType ((∅ : LocTypes).insert 0 .int) .empty recordProgram .unit := by
  change HasType _ _ (.project (.record recordLabels writes) (recordLabels.label 0)) _
  apply HasType.project (labels := recordLabels) (types := fun _ => .unit) 0
  apply HasType.record
  intro i
  by_cases left : i = 0 <;> simp only [writes, left, ite_true, ite_false]
  · exact .assign (.loc (by simp)) (.int 1)
  · exact .assign (.loc (by simp)) (.int 2)

theorem recordProgram_trace :
    Steps ⟨recordProgram, (∅ : Store).insert 0 zero⟩ ⟨.skip, (∅ : Store).insert 0 two⟩ := by
  have first : Step ⟨writes 0, (∅ : Store).insert 0 zero⟩ ⟨.skip, (∅ : Store).insert 0 one⟩ := by
    change Step ⟨.assign (.loc 0) one.val, _⟩ _
    simpa only [Finmap.insert_insert] using
      Step.assignValue one (s := (∅ : Store).insert 0 zero) (loc := 0) (by simp)
  let afterFirst := Function.update writes 0 .skip
  have second : Step ⟨afterFirst 1, (∅ : Store).insert 0 one⟩
      ⟨.skip, (∅ : Store).insert 0 two⟩ := by
    change Step ⟨.assign (.loc 0) two.val, _⟩ _
    simpa only [Finmap.insert_insert] using
      Step.assignValue two (s := (∅ : Store).insert 0 one) (loc := 0) (by simp)
  have firstReady : ∀ j : recordLabels.Index, j < 1 → IsValue (afterFirst j) := by
    intro j earlier
    have isZero : j = 0 := Fin.ext (Nat.lt_one_iff.mp earlier)
    subst j
    simpa only [afterFirst, Function.update_self] using IsValue.skip
  have noEarlier : ∀ j : recordLabels.Index, j < 0 → IsValue (writes j) := by
    intro j earlier
    exact (Nat.not_lt_zero j.val earlier).elim
  refine .head (.projectStep (.recordStep (labels := recordLabels) 0 noEarlier first)) ?_
  refine .head (.projectStep (.recordStep (labels := recordLabels) 1 firstReady second)) ?_
  have allReady : ∀ j : recordLabels.Index, IsValue (Function.update afterFirst 1 .skip j) := by
    intro j
    by_cases last : j = 1
    · subst j
      simpa only [Function.update_self] using IsValue.skip
    · rw [Function.update_of_ne last]
      apply firstReady
      have bounded := j.isLt
      change j.val < 2 at bounded
      have different : j.val ≠ 1 := fun h => last (Fin.ext h)
      change j.val < 1
      omega
  exact .single (.projectValue (labels := recordLabels) 0 allReady)

/-- Fresh names are chosen by the relation. This closed, well-typed source has
two distinct successors even from an empty store. -/
theorem allocation_nondeterministic :
    ∃ first second, Step ⟨.ref (.int 0), ∅⟩ first ∧
      Step ⟨.ref (.int 0), ∅⟩ second ∧ first ≠ second := by
  refine ⟨⟨.loc 0, (∅ : Store).insert 0 zero⟩, ⟨.loc 1, (∅ : Store).insert 1 zero⟩,
    .refValue zero Finmap.notMem_empty, .refValue zero Finmap.notMem_empty, ?_⟩
  intro equal
  exact Nat.zero_ne_one (Expr.loc.inj (congrArg Config.expr equal))

-- The same source name has a different scope in the scrutinee and each branch.
example :
    (RawExpr.matchSum (.var "x") "x" .int (.var "x") "y" .bool (.var "x")).resolve [] =
      .matchSum (.fvar "x") .int (.bvar 0) .bool (.fvar "x") := rfl

example : Stuck ⟨.deref (.loc 0), ∅⟩ := by
  constructor
  · intro value
    cases value
  · intro next step
    cases step with
    | derefValue lookup => rw [Finmap.lookup_empty] at lookup; contradiction
    | derefStep inner => cases inner

example : Stuck ⟨.assign (.int 0) (.ref (.int 1)), ∅⟩ := by
  constructor
  · intro value
    cases value
  · intro next step
    cases step with
    | assignLeft inner => cases inner

private def storedInt (s : Store) (loc : Loc) : Option Int :=
  s.lookup loc |>.bind fun value =>
    match value.val with
    | .int n => some n
    | _ => none

-- The executable trace makes the intermediate write visible before the second write.
#guard (do
    let first ← (Config.mk recordProgram ((∅ : Store).insert 0 zero)).reduce
    let second ← first.reduce
    let projected ← second.reduce
    let returned := match projected.expr with | .skip => projected.reduce.isNone | _ => false
    some (storedInt first.store 0, storedInt second.store 0, returned)) ==
  some (some 1, some 2, true)

-- A stuck first field prevents any step in the second field.
#guard (Config.mk (.record recordLabels (fun i =>
    if i = 0 then .deref (.loc 9) else .ref (.int 7))) ∅).reduce.isNone

-- A record projects by label after both fields are values.
#guard ((Config.mk (.project (.record recordLabels (fun i => .int (Int.ofNat i.val))) "second")
    ∅).reduce.bind fun next => match next.expr with | .int n => some n | _ => none) == some 1

-- Starting from a nonempty store chooses max + 1 and retains the original binding.
#guard ((Config.mk (.ref (.int 3)) ((∅ : Store).insert 7 two)).reduce.bind fun next =>
    match next.expr with
    | .loc address => some (address, storedInt next.store address, storedInt next.store 7)
    | _ => none) == some (8, some 3, some 2)

end Silmaril.Courses.Cambridge.L3.Examples
