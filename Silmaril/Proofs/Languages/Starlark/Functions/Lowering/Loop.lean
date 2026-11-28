module

public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Preservation
public import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Lowering

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration

private theorem enterMatch {s t : State} (same : StateMatch 0 s t) (guard : Option Address) :
    StateMatch 0 (enterIterator s guard) (enterIterator t guard) := by
  cases guard with
  | none => exact same
  | some address =>
    exact ⟨same.heap, congrArg (address :: ·) same.iterators, same.slots, same.bindings⟩

private theorem restoreMatch {source lowered : Outcome Flow} (same : OutcomeMatch 0 source lowered)
    {original saved : List Address} (stack : original = saved) :
    OutcomeMatch 0 (restoreIterators original source) (restoreIterators saved lowered) := by
  cases same with
  | ok related => exact .ok ⟨related.heap, stack, related.slots, related.bindings⟩
  | error related => exact .error ⟨related.heap, stack, related.slots, related.bindings⟩

private theorem resumeMatch {α β : Type} {source lowered : Outcome α}
    {sourceNext loweredNext : α → Meaning β} (same : OutcomeMatch 0 source lowered)
    (next : ∀ value {s t}, StateMatch 0 s t → OutcomeMatch 0 (sourceNext value s) (loweredNext value t)) :
    OutcomeMatch 0 (Outcome.resume source sourceNext) (Outcome.resume lowered loweredNext) := by
  cases same with
  | ok related => exact next _ related
  | error related => exact .error related

private theorem unpackValueMatch (arity : Nat) (value : Value) {s t : State}
    (same : StateMatch 0 s t) : OutcomeMatch 0 (unpackValue arity value s) (unpackValue arity value t) := by
  have acquired := frameRun (acquireAction value).1 same
  have kept := (acquireAction value).2 s
  simp only [unpackValue]
  rw [acquired]
  cases read : acquireIterator value s with
  | error error next =>
    rw [read] at kept
    exact .error (scopeTransport same kept)
  | ok iterator next =>
    rw [read] at kept
    obtain ⟨_, cursor⟩ := iterator
    have related := scopeTransport same kept
    change StateMatch 0 next (rebind next t.bindings) at related
    by_cases size : cursor.remaining = arity
    · simpa [mapFrame, size] using OutcomeMatch.ok (value := cursor.collect) related
    · simpa [mapFrame, size] using OutcomeMatch.error
        (error := .unpackArity arity cursor.remaining) related

mutual
private theorem bindTargetMatch (target : LoopTarget) (value : Value) {s t : State}
    (same : StateMatch 0 s t) : OutcomeMatch 0 (bindTarget target value s) (bindTarget target value t) := by
  cases target with
  | name name =>
    simp only [bindTarget]
    exact .ok (StateMatch.write same name value)
  | sequence children =>
    simp only [bindTarget]
    exact resumeMatch (unpackValueMatch children.length value same)
      (fun values _ _ related => bindTargetsMatch children values related)
termination_by sizeOf target
decreasing_by simp_wf <;> omega

private theorem bindTargetsMatch (targets : List LoopTarget) (values : List Value) {s t : State}
    (same : StateMatch 0 s t) : OutcomeMatch 0 (bindTargets targets values s) (bindTargets targets values t) := by
  cases targets with
  | nil => simp only [bindTargets]; exact .ok same
  | cons target rest =>
    cases values with
    | nil => simp only [bindTargets]; exact .ok same
    | cons value values =>
      rw [bindTargets.eq_def (target :: rest) (value :: values) s,
        bindTargets.eq_def (target :: rest) (value :: values) t]
      exact resumeMatch (bindTargetMatch target value same)
        (fun _ _ _ related => bindTargetsMatch rest values related)
termination_by sizeOf targets
decreasing_by all_goals (simp_wf <;> omega)
end

theorem preservesAssignTarget {program : Program} {available : List DeclarationId} {state : State}
    {rhs : Languages.Starlark.Functions.Lowering.Expr} {out : Outcome Value}
    (ran : Evaluates program available state rhs out) (free : ScratchFree state)
    (target : LoopTarget) (start : Nat) :
    OutcomeMatch 0 (denoteBody program available (.assignTargetExpr target rhs) state)
      (denoteBody program available (lowerAssignTarget target rhs start).code state) := by
  have staged := stage_preserves ran free start
  rw [denoteBody]
  change OutcomeMatch 0 (Outcome.resume (denoteExpr program available rhs state) fun value next =>
    Outcome.resume (bindTarget target value next) fun () => pure Flow.next) _
  rw [denoteExpr_eq_of_evaluates ran]
  simp only [lowerAssignTarget]
  cases out with
  | error error s =>
    obtain ⟨final, evaluated, similar⟩ := staged
    rw [denoteBody, evaluated]
    exact .error similar
  | ok value s =>
    obtain ⟨final, evaluated, similar, saved⟩ := staged
    rw [denoteBody, evaluated]
    change OutcomeMatch 0 _ (denoteBody program available
      (.assignTargetExpr target (.atom (.read (.bound (temporary start))))) final)
    rw [denoteBody]
    change OutcomeMatch 0 _
      (Outcome.resume (denoteExpr program available (.atom (scratchRead start)) final) fun result next =>
        Outcome.resume (bindTarget target result next) fun () => pure Flow.next)
    have readBack : denoteExpr program available (.atom (scratchRead start)) final = .ok value final := by
      unfold denoteExpr
      rw [denoteExprWith.eq_def]
      exact saved
    rw [readBack]
    change OutcomeMatch 0
      (Outcome.resume (bindTarget target value s) fun () => pure Flow.next)
      (Outcome.resume (bindTarget target value final) fun () => pure Flow.next)
    exact resumeMatch (bindTargetMatch target value similar) (fun () _ _ related => .ok related)

private theorem cursorMatch (sourceBody loweredBody : Meaning Flow)
    (bodyMatch : ∀ s t, StateMatch 0 s t → OutcomeMatch 0 (sourceBody s) (loweredBody t))
    (target : LoopTarget) (cursor : Cursor) (s t : State) (same : StateMatch 0 s t) :
    OutcomeMatch 0 (denoteCursor target sourceBody cursor s) (denoteCursor target loweredBody cursor t) := by
  rw [denoteCursor.eq_def target sourceBody cursor s, denoteCursor.eq_def target loweredBody cursor t]
  cases step : cursor.advance with
  | none => exact .ok same
  | some item =>
    obtain ⟨value, rest⟩ := item
    dsimp only
    have bound := bindTargetMatch target value same
    generalize bindTarget target value s = source at bound ⊢
    generalize bindTarget target value t = lowered at bound ⊢
    cases bound with
    | error next => exact .error next
    | ok afterBind =>
      rename_i boundValue u v
      cases boundValue
      simp only [Outcome.resume]
      have related := bodyMatch _ _ afterBind
      generalize sourceBody u = source at related ⊢
      generalize loweredBody v = lowered at related ⊢
      cases related with
      | ok next =>
        rename_i flow s' t'
        cases flow with
        | next | continueLoop => exact cursorMatch sourceBody loweredBody bodyMatch target rest s' t' next
        | breakLoop | returned _ => exact .ok next
      | error next => exact .error next
termination_by cursor.remaining
decreasing_by all_goals exact Cursor.advance_decreases step

private theorem forInMatch (sourceBody loweredBody : Meaning Flow)
    (bodyMatch : ∀ s t, StateMatch 0 s t → OutcomeMatch 0 (sourceBody s) (loweredBody t))
    (target : LoopTarget) (value : Value) {s t : State} (same : StateMatch 0 s t) :
    OutcomeMatch 0 (denoteForIn target sourceBody (.ok value s))
      (denoteForIn target loweredBody (.ok value t)) := by
  have acquired := frameRun (acquireAction value).1 same
  have kept := (acquireAction value).2 s
  simp only [denoteForIn, Outcome.resume]
  rw [acquired]
  cases read : acquireIterator value s with
  | error error next =>
    rw [read] at kept
    exact .error (scopeTransport same kept)
  | ok iterator next =>
    rw [read] at kept
    obtain ⟨guard, cursor⟩ := iterator
    have related := scopeTransport same kept
    exact restoreMatch
      (cursorMatch sourceBody loweredBody bodyMatch target cursor _ _ (enterMatch related guard)) related.iterators

theorem preservesForIn {program : Program} {available : List DeclarationId} {state : State}
    {iterable : Languages.Starlark.Functions.Lowering.Expr} {out : Outcome Value}
    (ran : Evaluates program available state iterable out) (free : ScratchFree state)
    (target : LoopTarget) (sourceBody loweredBody : Body)
    (bodyMatch : ∀ s t, StateMatch 0 s t → OutcomeMatch 0
      (denoteBody program available sourceBody s) (denoteBody program available loweredBody t))
    (start : Nat) :
    OutcomeMatch 0 (denoteBody program available (.forInExpr target iterable sourceBody) state)
      (denoteBody program available (lowerForIn target iterable loweredBody start).code state) := by
  have staged := stage_preserves ran free start
  rw [denoteBody]
  change OutcomeMatch 0 (denoteForIn target (denoteBody program available sourceBody)
    (denoteExpr program available iterable state)) _
  rw [denoteExpr_eq_of_evaluates ran]
  simp only [lowerForIn]
  cases out with
  | error error s =>
    obtain ⟨final, evaluated, similar⟩ := staged
    rw [denoteBody, evaluated]
    exact .error similar
  | ok value s =>
    obtain ⟨final, evaluated, similar, saved⟩ := staged
    rw [denoteBody, evaluated]
    change OutcomeMatch 0 _ (denoteBody program available
      (.forIn target (.read (.bound (temporary start))) loweredBody) final)
    rw [denoteBody]
    change OutcomeMatch 0 _ (denoteForIn target (denoteBody program available loweredBody)
      (denote (scratchRead start) final))
    rw [saved]
    exact forInMatch _ _ bodyMatch target value similar

private theorem unpack_slots (arity : Nat) (value : Value) (state : State) :
    (finishState (unpackValue arity value state)).slots = state.slots := by
  have kept := (acquireAction value).2 state
  unfold unpackValue
  cases read : acquireIterator value state with
  | error =>
    rw [read] at kept
    exact kept.2
  | ok iterator next =>
    rw [read] at kept
    obtain ⟨_, cursor⟩ := iterator
    by_cases arityCheck : cursor.remaining = arity <;> simpa only [arityCheck, ite_true, ite_false, finishState] using kept.2

mutual
theorem bindTarget_slots (target : LoopTarget) (value : Value) (state : State) :
    (finishState (bindTarget target value state)).slots = state.slots := by
  rw [bindTarget.eq_def]
  cases target with
  | name name => exact write_slots state name value
  | sequence children =>
    have kept := unpack_slots children.length value state
    cases ran : unpackValue children.length value state with
    | error =>
      rw [ran] at kept
      simpa only [ran, Outcome.resume, finishState] using kept
    | ok values next =>
      rw [ran] at kept
      simpa only [ran, Outcome.resume, finishState] using (bindTargets_slots children values next).trans kept
termination_by sizeOf target
decreasing_by simp_wf <;> omega

private theorem bindTargets_slots (targets : List LoopTarget) (values : List Value) (state : State) :
    (finishState (bindTargets targets values state)).slots = state.slots := by
  cases targets with
  | nil => rw [bindTargets]; rfl
  | cons target rest =>
    cases values with
    | nil => rw [bindTargets]; rfl
    | cons value values =>
      rw [bindTargets]
      have kept := bindTarget_slots target value state
      cases ran : bindTarget target value state with
      | error =>
        rw [ran] at kept
        simpa only [ran, Outcome.resume, finishState] using kept
      | ok _ next =>
        rw [ran] at kept
        simpa only [ran, Outcome.resume, finishState] using (bindTargets_slots rest values next).trans kept
termination_by sizeOf targets
decreasing_by all_goals (simp_wf <;> omega)
end

private theorem cursor_exact (target : LoopTarget) (source lowered : Meaning Flow)
    (body : ∀ s, ScratchFree s → source s = lowered s ∧ (finishState (source s)).slots = s.slots)
    (cursor : Cursor) (state : State) (free : ScratchFree state) :
    denoteCursor target source cursor state = denoteCursor target lowered cursor state ∧
      (finishState (denoteCursor target source cursor state)).slots = state.slots := by
  rw [denoteCursor.eq_def target source cursor state, denoteCursor.eq_def target lowered cursor state]
  cases step : cursor.advance with
  | none => exact ⟨rfl, rfl⟩
  | some item =>
    obtain ⟨value, rest⟩ := item
    dsimp only
    have slots := bindTarget_slots target value state
    cases ran : bindTarget target value state with
    | error error stopped =>
      rw [ran] at slots
      simp only [Outcome.resume]
      exact ⟨True.intro, slots⟩
    | ok _ next =>
      rw [ran] at slots
      have ⟨equal, kept⟩ := body next (fun index => (congrFun slots (temporary index)).trans (free index))
      simp only [Outcome.resume, ← equal]
      cases runBody : source next with
      | error error stopped =>
        rw [runBody] at kept
        exact ⟨rfl, kept.trans slots⟩
      | ok flow final =>
        rw [runBody] at kept
        have finalSlots := kept.trans slots
        cases flow with
        | next | continueLoop =>
          obtain ⟨out, after⟩ := cursor_exact target source lowered body rest final
            (fun index => (congrFun finalSlots (temporary index)).trans (free index))
          exact ⟨out, after.trans finalSlots⟩
        | breakLoop | returned => exact ⟨rfl, finalSlots⟩
termination_by cursor.remaining
decreasing_by all_goals exact Cursor.advance_decreases step

theorem forIn_exact (target : LoopTarget) (source lowered : Meaning Flow)
    (body : ∀ s, ScratchFree s → source s = lowered s ∧ (finishState (source s)).slots = s.slots)
    (operand : Outcome Value) (free : ScratchFree (finishState operand)) :
    denoteForIn target source operand = denoteForIn target lowered operand ∧
      (finishState (denoteForIn target source operand)).slots = (finishState operand).slots := by
  cases operand with
  | error => exact ⟨rfl, rfl⟩
  | ok value state =>
    have kept := (acquireAction value).2 state
    simp only [denoteForIn, Outcome.resume]
    cases ran : acquireIterator value state with
    | error error stopped =>
      rw [ran] at kept
      exact ⟨rfl, kept.2⟩
    | ok iterator next =>
      rw [ran] at kept
      obtain ⟨guard, cursor⟩ := iterator
      have slots : (enterIterator next guard).slots = state.slots := by
        cases guard <;> exact kept.2
      obtain ⟨equal, after⟩ := cursor_exact target source lowered body cursor (enterIterator next guard)
        (fun index => (congrFun slots (temporary index)).trans (free index))
      dsimp only
      refine ⟨congrArg (restoreIterators next.iterators) equal, ?_⟩
      have cleaned : ∀ out : Outcome Flow,
          (finishState (restoreIterators next.iterators out)).slots = (finishState out).slots :=
        fun out => by cases out <;> rfl
      exact (cleaned _).trans (after.trans slots)

end Silmaril.Proofs.Languages.Starlark.Functions.Lowering
