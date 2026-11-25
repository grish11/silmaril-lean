module

public import Silmaril.Languages.Starlark.Lists.Iteration.Operational.Defs
public import Silmaril.Languages.Starlark.Lists.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.Iteration

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration

private def meaning : Work → Meaning Flow
  | .suite code => denoteSuite code
  | .items target body remaining => denoteItems target (denoteSuite body) remaining

private theorem branch_apply {depth : Nat} (flag : Bool) (yes no : Suite depth) (state : State) :
    (if flag then denoteSuite yes else denoteSuite no) state =
      denoteSuite (if flag then yes else no) state := by
  cases flag <;> rfl

private theorem meaning_of_runs {s : State} {job : Work} {out : Outcome Flow}
    (h : Runs s job out) : meaning job s = out := by
  induction h <;> (try have evaluated := (eval_iff_denote _ _ _).mp (by assumption)) <;>
    simp_all [meaning, denoteSuite, denoteItems, Outcome.resume, branch_apply]
  case seqStop signal _ _ _ =>
    cases signal <;> simp_all <;> rfl
  case itemsAdvance =>
    rcases ‹_ ∨ _› with rfl | rfl <;> simp_all

theorem denoteSuite_eq_of_runs {depth : Nat} {s : State} {code : Suite depth} {out : Outcome Flow}
    (h : Runs s (.suite code) out) : denoteSuite code s = out :=
  meaning_of_runs h

private theorem items_run {depth : Nat} (body : Suite depth)
    (bodyRuns : ∀ s, Runs s (.suite body) (denoteSuite body s)) (target : Binding)
    (remaining : List Value) (state : State) :
    Runs state (.items target body remaining) (denoteItems target (denoteSuite body) remaining state) := by
  induction remaining generalizing state with
  | nil => exact .itemsDone
  | cons value rest ih =>
    cases h : denoteSuite body (state.write target value) with
    | error error next =>
      rw [denoteItems, h]
      exact .itemsError (h ▸ bodyRuns (state.write target value))
    | ok flow next =>
      cases flow with
      | next =>
        rw [denoteItems, h]
        exact .itemsAdvance (h ▸ bodyRuns (state.write target value)) (Or.inl rfl) (ih next)
      | continueLoop =>
        rw [denoteItems, h]
        exact .itemsAdvance (h ▸ bodyRuns (state.write target value)) (Or.inr rfl) (ih next)
      | breakLoop =>
        rw [denoteItems, h]
        exact .itemsBreak (h ▸ bodyRuns (state.write target value))
      | returned result =>
        rw [denoteItems, h]
        exact .itemsReturn (h ▸ bodyRuns (state.write target value))

theorem runs_denoteSuite {depth : Nat} (code : Suite depth) (state : State) :
    Runs state (.suite code) (denoteSuite code state) := by
  induction code generalizing state with
  | atomic stmt => exact .atomic ((eval_iff_denote _ _ _).mpr rfl)
  | seq first rest ihFirst ihRest =>
    rw [denoteSuite]
    cases h : denoteSuite first state with
    | error error next =>
      exact .seqError (h ▸ ihFirst state)
    | ok flow next =>
      cases flow with
      | next => exact .seq (h ▸ ihFirst state) (ihRest next)
      | breakLoop => exact .seqStop (h ▸ ihFirst state) (by intro equality; cases equality)
      | continueLoop => exact .seqStop (h ▸ ihFirst state) (by intro equality; cases equality)
      | returned result => exact .seqStop (h ▸ ihFirst state) (by intro equality; cases equality)
  | branch test yes no ihYes ihNo =>
    rw [denoteSuite]
    have tested : Eval state test (denote test state) := (eval_iff_denote _ _ _).mpr rfl
    cases h : Outcome.resume (denote test state) truth with
    | error error next => exact .branchError tested h
    | ok flag next =>
      cases flag
      · exact .branch tested h (ihNo next)
      · exact .branch tested h (ihYes next)
  | forIn target iterable body ihBody =>
    rw [denoteSuite]
    have evaluated : Eval state iterable (denote iterable state) := (eval_iff_denote _ _ _).mpr rfl
    cases h : Outcome.resume (denote iterable state) iterationSource with
    | error error next => exact .forError evaluated h
    | ok source next =>
      obtain ⟨address, elements⟩ := source
      exact .forIn evaluated h (items_run body ihBody target elements (pushIterator next address))
  | breakLoop => exact .breakLoop
  | continueLoop => exact .continueLoop
  | ret value => exact .ret ((eval_iff_denote _ _ _).mpr rfl)

end Silmaril.Proofs.Languages.Starlark.Lists.Iteration
