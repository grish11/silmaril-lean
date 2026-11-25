module

public import Silmaril.Courses.Cambridge.L2.Interpreter
public import Silmaril.Courses.Cambridge.L2.Metatheory.Progress

/-! # Correctness of executable L2 call-by-name reduction -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2

private theorem reduce_name_sound {s s' : Store} {e e' : Expr}
    (result : reduce .name s e = some (e', s')) :
    NameStep ⟨e, s⟩ ⟨e', s'⟩ := by
  fun_induction reduce .name s e generalizing e' s'
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
      | exact .appFun
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

/-- A configuration with no call-by-name successor. -/
def NameTerminal (config : Config) : Prop := ∀ next, ¬ NameStep config next

private theorem NameStep.not_value {e e' : Expr} {s s' : Store}
    (step : NameStep ⟨e, s⟩ ⟨e', s'⟩) : ¬ IsValue e :=
  fun value => by cases value <;> cases step

private theorem reduce_name_complete {before after : Config} (step : NameStep before after) :
    reduce .name before.store before.expr = some (after.expr, after.store) := by
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
      rw [reduce.eq_15]
      · simp [Expr.isValue_iff, inner.not_value, ih]
      · intro domain body equal
        exact inner.not_value (equal ▸ IsValue.lam domain body)
  | appFun => rfl
  | letStep inner ih => simp [reduce, Expr.isValue_iff, inner.not_value, ih]
  | letValue value => simp [reduce, Expr.isValue_iff.mpr value]

/-- The executable CBN reducer implements exactly the direct small-step rules,
including on untyped configurations. -/
theorem Config.reduce_name_iff_step {before after : Config} :
    before.reduce .name = some after ↔ NameStep before after := by
  cases before with
  | mk expr store =>
      constructor
      · intro result
        obtain ⟨⟨expr', store'⟩, reduced, rfl⟩ := Option.map_eq_some_iff.mp result
        exact reduce_name_sound reduced
      · intro step
        cases after
        simp [Config.reduce, reduce_name_complete step]

theorem Config.reduce_name_eq_none_iff_terminal {config : Config} :
    config.reduce .name = none ↔ NameTerminal config := by
  constructor
  · intro stopped next step
    rw [reduce_name_iff_step.mpr step] at stopped
    contradiction
  · intro terminal
    cases result : config.reduce .name with
    | none => rfl
    | some next => exact False.elim (terminal next (reduce_name_iff_step.mp result))

/-- Returning a configuration certifies a finite trace to a terminal state.
On untyped input that state may be stuck. -/
theorem runFuel_name_returns_terminal {fuel : Nat} {before after : Config}
    (result : runFuel .name fuel before = some after) :
    NameSteps before after ∧ NameTerminal after := by
  obtain ⟨trace, stopped⟩ := runFuel_returns result
  exact ⟨Relation.ReflTransGen.mono (fun _ _ step => Config.reduce_name_iff_step.mp step)
    _ _ trace, Config.reduce_name_eq_none_iff_terminal.mp stopped⟩

private theorem NameStep.preserves_type {Γ : TypeEnv} {before after : Config} {T : Ty}
    (step : NameStep before after) (typed : HasType Γ before.expr T) :
    HasType Γ after.expr T := by
  induction step generalizing T with
  | add a b _ => cases typed; exact .int (a + b)
  | ge a b _ => cases typed; exact .bool (a ≥ b)
  | binaryLeft _ ih =>
      cases typed with
      | add hl hr => exact .add (ih hl) hr
      | ge hl hr => exact .ge (ih hl) hr
  | binaryRight _ _ ih =>
      cases typed with
      | add hl hr => exact .add hl (ih hr)
      | ge hl hr => exact .ge hl (ih hr)
  | deref => cases typed; exact .int _
  | assignValue => cases typed; exact .skip
  | assignStep _ ih => cases typed with | assign present h => exact .assign present (ih h)
  | seqSkip => cases typed with | seq _ hr => exact hr
  | seqStep _ ih => cases typed with | seq hl hr => exact .seq (ih hl) hr
  | ifTrue => cases typed with | cond _ hy _ => exact hy
  | ifFalse => cases typed with | cond _ _ hn => exact hn
  | ifStep _ ih => cases typed with | cond hc hy hn => exact .cond (ih hc) hy hn
  | «while» => cases typed with | loop ht hb => exact .cond ht (.seq hb (.loop ht hb)) .skip
  | appLeft _ ih => cases typed with | app hf ha => exact .app (ih hf) ha
  | appFun =>
      cases typed with
      | app hf ha => cases hf with | lam hb => exact hb.beta ha
  | letStep _ ih => cases typed with | letE hv hb => exact .letE (ih hv) hb
  | letValue => cases typed with | letE hv hb => exact hb.beta hv
  | letRecFun => cases typed with | letRecFun hf hb => exact hb.beta hf.recClosure

private theorem NameStep.preserves_coverage {Γ : TypeEnv} {before after : Config}
    (step : NameStep before after) (covers : StoreCovers Γ before.store) :
    StoreCovers Γ after.store := by
  induction step
  case assignValue =>
    intro loc present
    exact Finmap.mem_insert.mpr (Or.inr (covers loc present))
  all_goals
    first
    | exact covers
    | apply_assumption
      exact covers

private theorem NameStep.preserves_closed {before after : Config}
    (step : NameStep before after) (closed : before.expr.Closed) :
    after.expr.Closed := by
  induction step with
  | add | ge | deref | assignValue => exact ⟨trivial, rfl⟩
  | appFun =>
      have noNames := Finset.union_eq_empty.mp closed.2
      exact ⟨Expr.beta_scoped closed.1.1 closed.1.2,
        Expr.beta_freeVars_empty noNames.1 noNames.2⟩
  | letValue =>
      have noNames := Finset.union_eq_empty.mp closed.2
      exact ⟨Expr.beta_scoped closed.1.2 closed.1.1,
        Expr.beta_freeVars_empty noNames.2 noNames.1⟩
  | letRecFun =>
      have noNames := Finset.union_eq_empty.mp closed.2
      exact ⟨Expr.beta_scoped closed.1.2 (Expr.recClosure_scoped closed.1.1),
        Expr.beta_freeVars_empty noNames.2 (Expr.recClosure_freeVars_empty noNames.1)⟩
  | binaryLeft _ ih =>
      have left := ih closed.binary_left
      exact ⟨⟨left.1, closed.1.2⟩,
        Finset.union_eq_empty.mpr ⟨left.2, closed.binary_right.2⟩⟩
  | binaryRight _ _ ih =>
      have right := ih closed.binary_right
      exact ⟨⟨closed.1.1, right.1⟩,
        Finset.union_eq_empty.mpr ⟨closed.binary_left.2, right.2⟩⟩
  | assignStep _ ih => exact ih closed
  | seqSkip =>
      exact ⟨closed.1.2, (Finset.union_eq_empty.mp closed.2).2⟩
  | seqStep _ ih =>
      have left := ih closed.seq_left
      exact ⟨⟨left.1, closed.1.2⟩,
        Finset.union_eq_empty.mpr ⟨left.2, (Finset.union_eq_empty.mp closed.2).2⟩⟩
  | ifTrue =>
      exact ⟨closed.1.2.1, (Finset.union_eq_empty.mp (Finset.union_eq_empty.mp closed.2).1).2⟩
  | ifFalse => exact ⟨closed.1.2.2, (Finset.union_eq_empty.mp closed.2).2⟩
  | ifStep _ ih =>
      have test := ih closed.cond_test
      have noNames := Finset.union_eq_empty.mp closed.2
      exact ⟨⟨test.1, closed.1.2⟩, Finset.union_eq_empty.mpr
        ⟨Finset.union_eq_empty.mpr ⟨test.2, (Finset.union_eq_empty.mp noNames.1).2⟩, noNames.2⟩⟩
  | «while» =>
      refine ⟨⟨closed.1.1, ⟨closed.1.2, closed.1⟩, trivial⟩, ?_⟩
      have noNames := Finset.union_eq_empty.mp closed.2
      simp only [Expr.freeVars, Finset.union_eq_empty, and_true]
      exact ⟨noNames.1, noNames.2, noNames⟩
  | appLeft _ ih =>
      have fn := ih closed.app_function
      exact ⟨⟨fn.1, closed.1.2⟩,
        Finset.union_eq_empty.mpr ⟨fn.2, closed.app_argument.2⟩⟩
  | letStep _ ih =>
      have value := ih closed.let_value
      exact ⟨⟨value.1, closed.1.2⟩,
        Finset.union_eq_empty.mpr ⟨value.2, (Finset.union_eq_empty.mp closed.2).2⟩⟩

-- A typed CBV step guarantees a CBN step, potentially to a different target.
private theorem Step.name_successor {Γ : TypeEnv} {before after : Config} {T : Ty}
    (step : Step before after) (typed : HasType Γ before.expr T) :
    ∃ next, NameStep before next := by
  induction step generalizing T with
  | add a b s => exact ⟨_, .add a b s⟩
  | ge a b s => exact ⟨_, .ge a b s⟩
  | binaryLeft _ ih =>
      cases typed with
      | add hl _ | ge hl _ =>
          obtain ⟨⟨_, _⟩, next⟩ := ih hl
          exact ⟨_, .binaryLeft next⟩
  | binaryRight value _ ih =>
      cases typed with
      | add _ hr | ge _ hr =>
          obtain ⟨⟨_, _⟩, next⟩ := ih hr
          exact ⟨_, .binaryRight value next⟩
  | deref found => exact ⟨_, .deref found⟩
  | assignValue present => exact ⟨_, .assignValue present⟩
  | assignStep _ ih =>
      cases typed with
      | assign _ he =>
          obtain ⟨⟨_, _⟩, next⟩ := ih he
          exact ⟨_, .assignStep next⟩
  | seqSkip => exact ⟨_, .seqSkip⟩
  | seqStep _ ih =>
      cases typed with
      | seq hl _ =>
          obtain ⟨⟨_, _⟩, next⟩ := ih hl
          exact ⟨_, .seqStep next⟩
  | ifTrue => exact ⟨_, .ifTrue⟩
  | ifFalse => exact ⟨_, .ifFalse⟩
  | ifStep _ ih =>
      cases typed with
      | cond ht _ _ =>
          obtain ⟨⟨_, _⟩, next⟩ := ih ht
          exact ⟨_, .ifStep next⟩
  | «while» => exact ⟨_, .while⟩
  | appLeft _ ih =>
      cases typed with
      | app hf _ =>
          obtain ⟨⟨_, _⟩, next⟩ := ih hf
          exact ⟨_, .appLeft next⟩
  | appRight value _ _ =>
      cases typed with
      | app hf _ =>
          obtain ⟨_, rfl⟩ := typed_function_value hf value
          exact ⟨_, .appFun⟩
  | appFun => exact ⟨_, .appFun⟩
  | letStep _ ih =>
      cases typed with
      | letE hv _ =>
          obtain ⟨⟨_, _⟩, next⟩ := ih hv
          exact ⟨_, .letStep next⟩
  | letValue ready => exact ⟨_, .letValue ready⟩
  | letRecFun => exact ⟨_, .letRecFun⟩

/-- A CBN return from a closed well-typed source with store coverage is a
value of the original type, with closedness and store coverage preserved. -/
theorem runFuel_name_returns_typed_value {fuel : Nat} {before after : Config}
    {Γ : TypeEnv} {T : Ty} (typed : HasType Γ before.expr T)
    (closed : before.expr.Closed) (covers : StoreCovers Γ before.store)
    (result : runFuel .name fuel before = some after) :
    IsValue after.expr ∧ HasType Γ after.expr T ∧
      after.expr.Closed ∧ StoreCovers Γ after.store := by
  obtain ⟨trace, terminal⟩ := runFuel_name_returns_terminal result
  have invariants : HasType Γ after.expr T ∧
      after.expr.Closed ∧ StoreCovers Γ after.store := by
    clear result terminal
    induction trace with
    | refl => exact ⟨typed, closed, covers⟩
    | tail _ step ih =>
        exact ⟨step.preserves_type ih.1, step.preserves_closed ih.2.1,
          step.preserves_coverage ih.2.2⟩
  refine ⟨?_, invariants⟩
  rcases progress invariants.1 invariants.2.1 invariants.2.2 with value | ⟨_, cbv⟩
  · exact value
  · obtain ⟨next, step⟩ := cbv.name_successor invariants.1
    exact (terminal next step).elim

-- A Boolean function position blocks CBN even when the argument could step.
example : let config : Config := ⟨.app (.bool true) (.loop (.bool false) .skip), ∅⟩
    runFuel .name 0 config = some config ∧ NameTerminal config := by
  have stopped : runFuel .name 0 ⟨.app (.bool true) (.loop (.bool false) .skip), ∅⟩ =
      some ⟨.app (.bool true) (.loop (.bool false) .skip), ∅⟩ := by decide
  exact ⟨stopped, (runFuel_name_returns_terminal stopped).2⟩

end Silmaril.Courses.Cambridge.L2
