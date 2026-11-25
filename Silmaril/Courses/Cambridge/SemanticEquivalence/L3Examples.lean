module

public import Silmaril.Courses.Cambridge.SemanticEquivalence.L3

/-! # Distinguishing two assignments (Exercise 43)

The context allocates and binds the reference named `l` before the hole.
The proof accounts for every possible fresh address.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.ContextualExamples

def write (n : Int) : RawExpr := .assign (.var "l") (.int n)

def referenceEnv : VarTypes :=
  { VarTypes.empty with free := (∅ : Finmap (fun _ : Var => Ty)).insert "l" (.ref .int) }

theorem write_typed (n : Int) : HasType ∅ referenceEnv ((write n).resolve []) .unit :=
  .assign (.fvar (by simp [referenceEnv])) (.int n)

def observeWrite : Context :=
  [.letBody "l" (.ref .int) (.ref (.int 0)),
    .seqLeft (.cond (.binary (.deref (.var "l")) .ge (.int 1))
      (.loop (.bool true) .skip) .skip)]

theorem observeWrite_closed (n : Int) : ClosedUnit (observeWrite.plug (write n)) :=
  .letE (.ref (.int 0)) (.seq (.assign (.bvar rfl) (.int n))
    (.cond (.ge (.deref (.bvar rfl)) (.int 1)) (.loop (.bool true) .skip) .skip))

private def cellValue (n : Int) : Value := ⟨.int n, .int n⟩
private def cell (loc : Loc) (n : Int) : Store := (∅ : Store).insert loc (cellValue n)
private def forever : Expr := .loop (.bool true) .skip
private def condition (ref : Expr) : Expr :=
  .cond (.binary (.deref ref) .ge (.int 1)) forever .skip
private def body (ref : Expr) (n : Int) : Expr :=
  .seq (.assign ref (.int n)) (condition ref)
private def allocated (loc : Loc) (n : Int) : Config :=
  ⟨.letE (.ref .int) (.loc loc) (body (.bvar 0) n), cell loc 0⟩

/-- A step whose destination is fixed by the source configuration. -/
private def ForcedStep (before after : Config) : Prop :=
  Step before after ∧ ∀ other, Step before other → other = after

private abbrev ForcedSteps := Relation.ReflTransGen ForcedStep

private theorem ForcedSteps.steps {before after : Config} (path : ForcedSteps before after) :
    Steps before after :=
  Relation.ReflTransGen.mono (fun _ _ step => step.1) _ _ path

private theorem ForcedSteps.not_diverges {before after : Config} (path : ForcedSteps before after)
    (stops : ¬ InfiniteTrace Step after) : ¬ InfiniteTrace Step before := by
  induction path with
  | refl => exact stops
  | tail _ edge ih =>
    apply ih
    intro diverges
    obtain ⟨next, step, rest⟩ := diverges.unfold
    exact stops (edge.2 next step ▸ rest)

private theorem ForcedSteps.unitReturns {before after : Config} (path : ForcedSteps before after)
    (finished : UnitReturns before) : UnitReturns after := by
  induction path with
  | refl => exact finished
  | tail _ edge ih =>
    obtain ⟨store, returns⟩ := ih
    rcases returns.cases_head with eq | ⟨next, step, rest⟩
    · cases eq
      have impossible := edge.1
      cases impossible
    · exact ⟨store, edge.2 next step ▸ rest⟩

private theorem allocate_step (loc : Loc) (n : Int) :
    Step ⟨(observeWrite.plug (write n)).resolve [], ∅⟩ (allocated loc n) :=
  .letStep (.refValue (cellValue 0) Finmap.notMem_empty)

private theorem allocate_only {n : Int} {next : Config}
    (step : Step ⟨(observeWrite.plug (write n)).resolve [], ∅⟩ next) :
    ∃ loc, next = allocated loc n := by
  change Step ⟨.letE (.ref .int) (.ref (.int 0)) (body (.bvar 0) n), ∅⟩ next at step
  cases step with
  | letValue value => cases value
  | letStep allocate =>
    generalize number : Expr.int 0 = initial at allocate
    cases allocate with
    | refStep inner =>
      rw [← number] at inner
      cases inner
    | refValue value _ =>
      have same : value = cellValue 0 := Subtype.ext number.symm
      cases same
      exact ⟨_, rfl⟩

private theorem allocated_forced (loc : Loc) (n : Int) :
    ForcedSteps (allocated loc n) ⟨.cond (.bool (n ≥ 1)) forever .skip, cell loc n⟩ := by
  have enter : ForcedStep (allocated loc n) ⟨body (.loc loc) n, cell loc 0⟩ := by
    refine ⟨.letValue (.loc loc), fun next step => ?_⟩
    change Step ⟨.letE (.ref .int) (.loc loc) (body (.bvar 0) n), cell loc 0⟩ next at step
    cases step with
    | letStep inner => cases inner
    | letValue => rfl
  have writeStep : ForcedStep ⟨body (.loc loc) n, cell loc 0⟩
      ⟨.seq .skip (condition (.loc loc)), cell loc n⟩ := by
    have present : loc ∈ cell loc 0 := Finmap.mem_insert.mpr (Or.inl rfl)
    have write : Step ⟨.assign (.loc loc) (.int n), cell loc 0⟩ ⟨.skip, cell loc n⟩ := by
      simpa only [cell, cellValue, Finmap.insert_insert] using Step.assignValue (cellValue n) present
    refine ⟨.seqStep write, fun next step => ?_⟩
    change Step ⟨.seq (.assign (.loc loc) (.int n)) (condition (.loc loc)), cell loc 0⟩ next at step
    cases step with
    | seqStep inner =>
      generalize number : Expr.int n = rhs at inner
      cases inner with
      | assignLeft inner => cases inner
      | assignRight inner =>
        rw [← number] at inner
        cases inner
      | assignValue value _ =>
        have same : value = cellValue n := Subtype.ext number.symm
        cases same
        simp only [cell, Finmap.insert_insert]
  have sequence : ForcedStep ⟨.seq .skip (condition (.loc loc)), cell loc n⟩
      ⟨condition (.loc loc), cell loc n⟩ := by
    refine ⟨.seqSkip, fun next step => ?_⟩
    cases step with
    | seqSkip => rfl
    | seqStep inner => cases inner
  have read : ForcedStep ⟨condition (.loc loc), cell loc n⟩
      ⟨.cond (.binary (.int n) .ge (.int 1)) forever .skip, cell loc n⟩ := by
    have present : (cell loc n).lookup loc = some (cellValue n) := Finmap.lookup_insert _
    refine ⟨.ifStep (.binaryLeft (.derefValue present)), fun next step => ?_⟩
    change Step ⟨.cond (.binary (.deref (.loc loc)) .ge (.int 1)) forever .skip, cell loc n⟩ next at step
    cases step with
    | ifStep inner =>
      cases inner with
      | binaryRight _ inner => cases inner
      | binaryLeft inner =>
        cases inner with
        | derefStep inner => cases inner
        | derefValue lookup => cases Option.some.inj (lookup.symm.trans present); rfl
  have compare : ForcedStep ⟨.cond (.binary (.int n) .ge (.int 1)) forever .skip, cell loc n⟩
      ⟨.cond (.bool (n ≥ 1)) forever .skip, cell loc n⟩ := by
    refine ⟨.ifStep (.ge n 1 _), fun next step => ?_⟩
    cases step with
    | ifStep inner =>
      cases inner with
      | ge => rfl
      | binaryLeft inner => cases inner
      | binaryRight _ inner => cases inner
  exact .head enter (.head writeStep (.head sequence (.head read (.single compare))))

private theorem zero_forced (loc : Loc) : ForcedSteps (allocated loc 0) ⟨.skip, cell loc 0⟩ := by
  refine (allocated_forced loc 0).tail ⟨.ifFalse, fun next step => ?_⟩
  change Step ⟨.cond (.bool false) forever .skip, cell loc 0⟩ next at step
  cases step with
  | ifFalse => rfl
  | ifStep inner => cases inner

private theorem one_forced (loc : Loc) : ForcedSteps (allocated loc 1) ⟨forever, cell loc 1⟩ := by
  refine (allocated_forced loc 1).tail ⟨.ifTrue, fun next step => ?_⟩
  change Step ⟨.cond (.bool true) forever .skip, cell loc 1⟩ next at step
  cases step with
  | ifTrue => rfl
  | ifStep inner => cases inner

private def LoopState (store : Store) (c : Config) : Prop :=
  c = ⟨forever, store⟩ ∨ c = ⟨.cond (.bool true) (.seq .skip forever) .skip, store⟩ ∨
    c = ⟨.seq .skip forever, store⟩

private theorem loop_step_closed {store : Store} {before after : Config}
    (source : LoopState store before) (step : Step before after) : LoopState store after := by
  rcases source with rfl | rfl | rfl
  · change Step ⟨.loop (.bool true) .skip, store⟩ after at step
    cases step
    exact Or.inr (Or.inl rfl)
  · cases step with
    | ifTrue => exact Or.inr (Or.inr rfl)
    | ifStep inner => cases inner
  · cases step with
    | seqSkip => exact Or.inl rfl
    | seqStep inner => cases inner

private theorem forever_diverges (store : Store) : InfiniteTrace Step ⟨forever, store⟩ := by
  apply InfiniteTrace.coinduct (LoopState store) ?_ (Or.inl rfl)
  rintro _ (rfl | rfl | rfl)
  · exact ⟨_, .while, Or.inr (Or.inl rfl)⟩
  · exact ⟨_, .ifTrue, Or.inr (Or.inr rfl)⟩
  · exact ⟨_, .seqSkip, Or.inl rfl⟩

private theorem forever_does_not_return (store : Store) : ¬ UnitReturns ⟨forever, store⟩ := by
  rintro ⟨lastStore, path⟩
  have along {before after : Config} (path : Steps before after) (starts : LoopState store before) :
      LoopState store after := by
    induction path with
    | refl => exact starts
    | tail _ step ih => exact loop_step_closed ih step
  have stays := along path (Or.inl rfl)
  rcases stays with equal | equal | equal <;> cases equal

theorem zero_returns : UnitReturns ⟨(observeWrite.plug (write 0)).resolve [], ∅⟩ :=
  ⟨cell 0 0, .head (allocate_step 0 0) (zero_forced 0).steps⟩

theorem zero_does_not_diverge : ¬ InfiniteTrace Step ⟨(observeWrite.plug (write 0)).resolve [], ∅⟩ := by
  intro diverges
  obtain ⟨_, step, rest⟩ := diverges.unfold
  obtain ⟨loc, rfl⟩ := allocate_only step
  apply (zero_forced loc).not_diverges _ rest
  intro infinite
  obtain ⟨_, impossible, _⟩ := infinite.unfold
  cases impossible

theorem one_diverges : InfiniteTrace Step ⟨(observeWrite.plug (write 1)).resolve [], ∅⟩ :=
  InfiniteTrace.of_steps (.head (allocate_step 0 1) (one_forced 0).steps)
    (forever_diverges (cell 0 1))

theorem one_does_not_return : ¬ UnitReturns ⟨(observeWrite.plug (write 1)).resolve [], ∅⟩ := by
  rintro ⟨store, path⟩
  rcases path.cases_head with equal | ⟨_, step, rest⟩
  · have impossible := congrArg Config.expr equal
    change Expr.letE (.ref .int) (.ref (.int 0)) (body (.bvar 0) 1) = .skip at impossible
    cases impossible
  · obtain ⟨loc, rfl⟩ := allocate_only step
    exact forever_does_not_return _ ((one_forced loc).unitReturns ⟨store, rest⟩)

/-- Exercise 43. The context tests the assigned cell and loops only after
the assignment of one. -/
theorem write_zero_not_equiv_write_one : ¬ ContextualEquiv ∅ referenceEnv .unit (write 0) (write 1) := by
  intro equiv
  rcases equiv.2.2 observeWrite (observeWrite_closed 0) (observeWrite_closed 1) with
    ⟨zeroInfinite, _⟩ | ⟨_, oneReturns⟩
  · exact zero_does_not_diverge zeroInfinite
  · exact one_does_not_return oneReturns

end Silmaril.Courses.Cambridge.L3.ContextualExamples
