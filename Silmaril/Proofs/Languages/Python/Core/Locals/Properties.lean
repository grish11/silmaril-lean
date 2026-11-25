module

public import Silmaril.Proofs.Languages.Python.Core.Locals.Execution

public section

namespace Silmaril.Proofs.Languages.Python.Core.Locals

open Silmaril.Languages.Python.Core.Locals Silmaril.Semantics.Operational

variable {slots : Nat} {store : Store slots} {source target : State slots}
  {label : Option (Event slots)} {rhs : Rhs slots} {next : Except (Error slots) (Rhs slots)}

theorem enter_answer (store : Store slots) (code : Code slots) :
    (State.enter store code).answer = code.eval store := by
  cases code <;> rfl

theorem enter_budget (store : Store slots) (code : Code slots) :
    (State.enter store code).budget = code.budget := by
  cases code <;> rfl

private theorem rhs_answer (step : rhs.Step store next) :
    rhs.eval store = next.bind (Rhs.eval store) := by
  induction step with
  | @arithmetic expr next step =>
    have preserves := Silmaril.Languages.Python.Core.Step.result_eq
      (Silmaril.Languages.Python.Core.Step.expr step)
    cases next <;> exact congrArg
      (fun (result : Silmaril.Languages.Python.Core.Completion) => (result.mapError Error.arithmetic : Result slots))
      preserves
  | load slot value loaded =>
    simp [Rhs.eval, Rhs.load, loaded, Except.bind, Silmaril.Languages.Python.Core.Expr.eval, Except.mapError]
  | unbound slot loaded => simp [Rhs.eval, Rhs.load, loaded, Except.bind]
  | @left op left right next step ih =>
    cases next <;> simp [Rhs.eval, Except.map, Except.bind, ih]
  | @right op left right next step ih =>
    cases next <;>
      simp [Rhs.eval, Except.map, Except.bind, ih, Silmaril.Languages.Python.Core.Expr.eval, Except.mapError]
  | @compute op left right result step =>
    have computed := Silmaril.Languages.Python.Core.BinOp.eval_iff.mpr step
    cases result <;>
      simp [Rhs.eval, Rhs.lift, Except.map, Except.bind, Except.mapError,
        Silmaril.Languages.Python.Core.Expr.eval, computed]
  | @logicalTest op left right next step ih =>
    cases next <;> simp [Rhs.eval, Except.map, Except.bind, ih]
  | logicalShort chosen =>
    simp [Rhs.eval, Except.bind, Except.mapError, Silmaril.Languages.Python.Core.Expr.eval, chosen]
  | logicalRight chosen =>
    simp [Rhs.eval, Except.bind, Except.mapError, Silmaril.Languages.Python.Core.Expr.eval, chosen]

theorem answer_eq (step : Step source label target) : source.answer = target.answer := by
  cases step with
  | @expression store rhs cont next reduced =>
    have result := rhs_answer reduced
    cases next with
    | ok rhs' =>
      change cont.finish store (rhs.eval store) = cont.finish store (rhs'.eval store)
      exact congrArg (fun value => cont.finish store value) result
    | error error =>
      change cont.finish store (rhs.eval store) = ⟨store, .error error⟩
      rw [result]
      cases cont <;> rfl
  | assign store slot value rest => exact (enter_answer (store.write slot value) rest).symm
  | takeYes store value yes no nonzero =>
    simpa [State.answer, Continuation.finish, Rhs.eval, Silmaril.Languages.Python.Core.Expr.eval,
      Except.mapError, nonzero] using (enter_answer store yes).symm
  | takeNo store yes no => exact (enter_answer store no).symm
  | ret | raise => rfl

private theorem rhs_decreases (step : rhs.Step store next) :
    match next with
    | .ok rhs' => rhs'.work < rhs.work
    | .error _ => True := by
  induction step with
  | @arithmetic expr next step =>
    have decreases := Silmaril.Languages.Python.Core.Step.decreases
      (Silmaril.Languages.Python.Core.Step.expr step)
    cases next with
    | error => trivial
    | ok expr' =>
      change expr'.work + 2 < expr.work + 2 at decreases
      change expr'.work < expr.work
      omega
  | load => simp [Rhs.work, Silmaril.Languages.Python.Core.Expr.work]
  | unbound => trivial
  | @left op left right next step ih =>
    cases next <;> simp [Except.map, Rhs.work] at ih ⊢
    omega
  | @right op left right next step ih =>
    cases next <;> simp [Except.map, Rhs.work] at ih ⊢
    omega
  | @compute op left right result step =>
    cases result <;> simp [Except.map, Rhs.lift, Rhs.work, Silmaril.Languages.Python.Core.Expr.work]
  | @logicalTest op left right next step ih =>
    cases next <;> simp [Except.map, Rhs.work] at ih ⊢
    omega
  | logicalShort => simp [Rhs.work, Silmaril.Languages.Python.Core.Expr.work]
  | logicalRight => simp [Rhs.work, Silmaril.Languages.Python.Core.Expr.work]

private theorem code_minBudget (code : Code slots) : 2 ≤ code.budget := by
  induction code with
  | ret rhs => simp [Code.budget]
  | assign slot rhs rest ih =>
    simp only [Code.budget]
    omega
  | branch test yes no yesIH noIH =>
    simp only [Code.budget]
    have upper := Nat.le_max_left yes.budget no.budget
    omega

private theorem cont_minBudget (cont : Continuation slots) : 2 ≤ cont.budget := by
  cases cont with
  | ret => simp [Continuation.budget]
  | assign slot rest =>
    simp only [Continuation.budget]
    have enough := code_minBudget rest
    omega
  | branch yes no =>
    simp only [Continuation.budget]
    have enough := code_minBudget yes
    have upper := Nat.le_max_left yes.budget no.budget
    omega

theorem decreases (step : Step source label target) : target.budget < source.budget := by
  cases step with
  | @expression store rhs cont next reduced =>
    have decrease := rhs_decreases reduced
    cases next with
    | ok rhs' => exact Nat.add_lt_add_right decrease cont.budget
    | error error =>
      have positive := cont_minBudget cont
      change 1 < rhs.work + cont.budget
      omega
  | assign store slot value rest =>
    rw [enter_budget]
    simp [State.budget, Rhs.work, Continuation.budget, Silmaril.Languages.Python.Core.Expr.work]
  | takeYes store value yes no nonzero =>
    rw [enter_budget]
    change yes.budget < 0 + (max yes.budget no.budget + 1)
    have upper := Nat.le_max_left yes.budget no.budget
    omega
  | takeNo store yes no =>
    rw [enter_budget]
    change no.budget < 0 + (max yes.budget no.budget + 1)
    have upper := Nat.le_max_right yes.budget no.budget
    omega
  | ret => simp [State.budget, Rhs.work, Continuation.budget, Silmaril.Languages.Python.Core.Expr.work]
  | raise => simp [State.budget]

theorem finishes_in_budget (state : State slots) :
    ∃ length, length ≤ state.budget ∧ StepsN (ordinary slots).step length state
      (.finished state.answer.store state.answer.result) := by
  induction state using (measure State.budget).wf.induction with
  | h state ih =>
    rcases progress state with ⟨label, target, edge⟩ | ⟨result, observed⟩
    · obtain ⟨length, bound, path⟩ := ih target (decreases edge)
      have less := decreases edge
      rw [answer_eq edge]
      exact ⟨length + 1, by omega, .cons ⟨label, edge⟩ path⟩
    · cases observed
      exact ⟨0, Nat.zero_le _, .nil _⟩

theorem noDiverges (state : State slots) : ¬ (ordinary slots).Diverges state := by
  obtain ⟨_, _, path⟩ := finishes_in_budget state
  exact StepsN.no_diverges_of_normal (sem := (model slots).semantics) path
    (detFrom state) (terminal slots (.finished _ _))

private theorem reach_answer (path : (ordinary slots).Reach source target) :
    source.answer = target.answer := by
  induction path with
  | refl => rfl
  | tail _ step ih =>
    obtain ⟨_, edge⟩ := step
    exact ih.trans (answer_eq edge)

theorem may_iff {outcome : Outcome (Result slots)} :
    (ordinary slots).May source outcome ↔ outcome = .returned source.answer.result := by
  constructor
  · rintro ⟨state, path, observed⟩
    cases observed
    exact congrArg Outcome.returned (congrArg Answer.result (reach_answer path)).symm
  · rintro rfl
    obtain ⟨_, _, path⟩ := finishes_in_budget source
    exact ⟨_, path.reach, .finished _ _⟩

theorem model_may_iff {code : Code slots} {outcome : Outcome (Result slots)} :
    (model slots).May code outcome ↔ outcome = .returned (code.eval (Store.empty slots)).result := by
  constructor
  · rintro ⟨state, initial, observed⟩
    change state = State.enter (Store.empty slots) code at initial
    subst state
    simpa only [enter_answer] using may_iff.mp observed
  · intro observed
    exact ⟨_, rfl, may_iff.mpr (by simpa only [enter_answer] using observed)⟩

theorem closed_may_iff (body : Silmaril.Languages.Python.Core.Body)
    (admitted : Silmaril.Languages.Python.Core.Profile.arithmetic.supports body.value)
    (result : Silmaril.Languages.Python.Core.Completion) (slots : Nat) :
    (model slots).May (.ret (.arithmetic body.value)) (.returned (result.mapError .arithmetic)) ↔
      (Silmaril.Languages.Python.Core.model .arithmetic).May body (.returned result) := by
  rw [model_may_iff, Silmaril.Languages.Python.Core.model_may_iff]
  change (Outcome.returned (result.mapError Error.arithmetic) : Outcome (Result slots)) =
    .returned (body.value.eval.mapError .arithmetic) ↔ _
  rw [and_iff_right admitted, Outcome.returned.injEq, Outcome.returned.injEq]
  constructor
  · intro same
    cases result <;> cases computed : body.value.eval <;> simp [computed, Except.mapError] at same ⊢
    exact same
  · intro same
    rw [same]

theorem run_exact (oracle : Oracle (model slots).semantics)
    (known : ∀ state, oracle.pick state ≠ .stop .unknown) (state : State slots)
    {fuel : Nat} (enough : state.budget ≤ fuel) :
    oracle.run state fuel =
      .stop (.finished state.answer.store state.answer.result) (.observed (.returned state.answer.result)) := by
  obtain ⟨_, bound, path⟩ := finishes_in_budget state
  exact Oracle.run_complete oracle path (.finished _ _) (bound.trans enough)
    (detFrom state) (terminal slots) (WithUB.ofOpSem_safe _ _) (fun {state} _ => known state)

end Silmaril.Proofs.Languages.Python.Core.Locals
