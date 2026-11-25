module

public import Silmaril.Courses.Cambridge.L2.Interpreter
public import Silmaril.Courses.Cambridge.L2.Metatheory.Progress

/-! # Correctness of executable L2 call-by-value reduction -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2

private theorem reduce_value_sound {s s' : Store} {e e' : Expr}
    (result : reduce .value s e = some (e', s')) :
    Step ⟨e, s⟩ ⟨e', s'⟩ := by
  fun_induction reduce .value s e generalizing e' s'
  all_goals try contradiction
  all_goals try
    first
    | obtain ⟨inner, reduced, equal⟩ := Option.map_eq_some_iff.mp result
      rcases inner with ⟨next, store⟩
      cases equal
      first
      | exact .binaryLeft (by apply_assumption; exact reduced)
      | exact .binaryRight (Expr.isValue_iff.mp (by assumption)) (by apply_assumption; exact reduced)
      | exact .ifStep (by apply_assumption; exact reduced)
      | exact .assignStep (by apply_assumption; exact reduced)
      | exact .seqStep (by apply_assumption; exact reduced)
      | exact .appLeft (by apply_assumption; exact reduced)
      | exact .appRight (Expr.isValue_iff.mp (by first | assumption | rfl))
          (by apply_assumption; exact reduced)
      | exact .letStep (by apply_assumption; exact reduced)
    | obtain ⟨n, found, equal⟩ := Option.map_eq_some_iff.mp result
      cases equal
      exact .deref found
    | cases result
      first
      | exact .add _ _ _
      | exact .ge _ _ _
      | exact .ifTrue
      | exact .ifFalse
      | exact .seqSkip
      | exact .while
      | exact .appFun (Expr.isValue_iff.mp (by assumption))
      | exact .letValue (Expr.isValue_iff.mp (by assumption))
      | exact .letRecFun
  case case8 loc n =>
    obtain ⟨next, updated, equal⟩ := Option.map_eq_some_iff.mp result
    cases equal
    by_cases present : loc ∈ s
    · rw [L1.Store.update_eq_some _ _ _ present] at updated
      cases updated
      exact .assignValue present
    · simp [L1.Store.update_eq_none _ _ _ present] at updated

private theorem Step.not_value {e e' : Expr} {s s' : Store}
    (step : Step ⟨e, s⟩ ⟨e', s'⟩) : ¬ IsValue e :=
  fun value => value_terminal value _ step

private theorem reduce_value_complete {before after : Config} (step : Step before after) :
    reduce .value before.store before.expr = some (after.expr, after.store) := by
  induction step with
  | add | ge | seqSkip | ifTrue | ifFalse | «while» | letRecFun => rfl
  | binaryLeft inner ih =>
      have nonvalue := inner.not_value
      rw [reduce.eq_3]
      · simp [Expr.isValue_iff, nonvalue, ih]
      all_goals
        intro a b leftEq _ _
        exact nonvalue (leftEq ▸ IsValue.int a)
  | binaryRight value inner ih =>
      have nonvalue := inner.not_value
      rw [reduce.eq_3]
      · simp [Expr.isValue_iff.mpr value, ih]
      all_goals
        intro a b _ _ rightEq
        exact nonvalue (rightEq ▸ IsValue.int b)
  | deref found => simp [reduce, found]
  | assignValue present => simp [reduce, L1.Store.update_eq_some _ _ _ present]
  | assignStep inner ih =>
      rw [reduce.eq_8]
      · simp [ih]
      · intro n equal
        exact inner.not_value (equal ▸ IsValue.int n)
  | seqStep inner ih =>
      rw [reduce.eq_11]
      · simp [ih]
      · intro equal
        exact inner.not_value (equal ▸ IsValue.skip)
  | ifStep inner ih =>
      rw [reduce.eq_6]
      · simp [ih]
      · intro equal
        exact inner.not_value (equal ▸ IsValue.bool true)
      · intro equal
        exact inner.not_value (equal ▸ IsValue.bool false)
  | appLeft inner ih =>
      rw [reduce.eq_16]
      · simp [Expr.isValue_iff, inner.not_value, ih]
      · intro domain body equal
        exact inner.not_value (equal ▸ IsValue.lam domain body)
  | appRight value inner ih =>
      cases value with
      | lam =>
          simp [reduce, Expr.isValue_iff, inner.not_value, ih]
      | int | bool | skip =>
          rw [reduce.eq_16]
          · simp [Expr.isValue, ih]
          · intros
            contradiction
  | appFun value => simp [reduce, Expr.isValue_iff.mpr value]
  | letStep inner ih => simp [reduce, Expr.isValue_iff, inner.not_value, ih]
  | letValue value => simp [reduce, Expr.isValue_iff.mpr value]

/-- The executable CBV reducer implements exactly the direct small-step rules,
including on untyped configurations. -/
theorem Config.reduce_value_iff_step {before after : Config} :
    before.reduce .value = some after ↔ Step before after := by
  cases before with
  | mk expr store =>
      constructor
      · intro result
        obtain ⟨⟨expr', store'⟩, reduced, rfl⟩ := Option.map_eq_some_iff.mp result
        exact reduce_value_sound reduced
      · intro step
        cases after
        simp [Config.reduce, reduce_value_complete step]

theorem Config.reduce_value_eq_none_iff_terminal {config : Config} :
    config.reduce .value = none ↔ Terminal config := by
  constructor
  · intro stopped next step
    rw [reduce_value_iff_step.mpr step] at stopped
    contradiction
  · intro terminal
    cases result : config.reduce .value with
    | none => rfl
    | some next => exact False.elim (terminal next (reduce_value_iff_step.mp result))

/-- Returning a configuration certifies a finite trace to a terminal state.
On untyped input that state may be stuck. -/
theorem runFuel_value_returns_terminal {fuel : Nat} {before after : Config}
    (result : runFuel .value fuel before = some after) :
    Steps before after ∧ Terminal after := by
  obtain ⟨trace, stopped⟩ := runFuel_returns result
  exact ⟨Relation.ReflTransGen.mono (fun _ _ step => Config.reduce_value_iff_step.mp step)
    _ _ trace, Config.reduce_value_eq_none_iff_terminal.mp stopped⟩

/-- With the hypotheses of L2 safety, a CBV return is a value of the original
type. It retains closedness and needs only the original store coverage. -/
theorem runFuel_value_returns_typed_value {fuel : Nat} {before after : Config}
    {Γ : TypeEnv} {T : Ty} (typed : HasType Γ before.expr T)
    (closed : before.expr.Closed) (covers : StoreCovers Γ before.store)
    (result : runFuel .value fuel before = some after) :
    IsValue after.expr ∧ HasType Γ after.expr T ∧
      after.expr.Closed ∧ StoreCovers Γ after.store := by
  obtain ⟨trace, terminal⟩ := runFuel_value_returns_terminal result
  have invariants : HasType Γ after.expr T ∧
      after.expr.Closed ∧ StoreCovers Γ after.store := by
    clear result terminal
    induction trace with
    | refl => exact ⟨typed, closed, covers⟩
    | tail _ step ih => exact type_preservation ih.1 ih.2.1 ih.2.2 step
  refine ⟨?_, invariants⟩
  rcases progress invariants.1 invariants.2.1 invariants.2.2 with value | ⟨next, step⟩
  · exact value
  · exact False.elim (terminal next step)

-- The executable return convention also includes stuck untyped input.
example : let missing : Config := ⟨.deref "missing", ∅⟩
    runFuel .value 0 missing = some missing ∧ Stuck missing := by
  have stopped : runFuel .value 0 ⟨.deref "missing", ∅⟩ =
      some ⟨.deref "missing", ∅⟩ := by decide
  refine ⟨stopped, ?_, (runFuel_value_returns_terminal stopped).2⟩
  intro value
  cases value

end Silmaril.Courses.Cambridge.L2
