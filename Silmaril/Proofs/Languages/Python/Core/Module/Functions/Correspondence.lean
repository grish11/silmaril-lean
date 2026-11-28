module

public import Silmaril.Languages.Python.Core.Module.Functions.Defs
public import Silmaril.Languages.Python.Core.Closure.Dispatch.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Module.Functions

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Module.Functions

theorem publish_iff {session updated : Session} {table : Executor.CodeTable} {name : GlobalName}
    {function : TopFunction} : session.publish table name function = .ok updated ↔
      (∃ definition, Dispatch.Resolves table function.ref definition) ∧
        updated = session.bindGlobal name function.value := by
  cases resolved : Dispatch.resolve table function.ref with
  | error error =>
    simp only [Session.publish, resolved, Except.map, reduceCtorEq, false_iff, not_and]
    rintro ⟨definition, found⟩
    have lookup := Dispatch.resolve_iff.mpr found
    rw [resolved] at lookup
    contradiction
  | ok definition =>
    have found : ∃ definition, Dispatch.Resolves table function.ref definition :=
      ⟨definition, Dispatch.resolve_iff.mp resolved⟩
    simp [Session.publish, resolved, Except.map, found, eq_comm]

private theorem selected {invocation : Invocation} {observation : Observation}
    (ran : invocation.finish? = some observation) :
    Settles invocation.globals invocation.lists invocation.destination invocation.state observation := by
  obtain ⟨globals, destination, state, lists⟩ := invocation
  cases state with
  | running heap frame body stack => simp [Invocation.finish?] at ran
  | delivering heap stack result => simp [Invocation.finish?] at ran
  | receiving heap caller stack result => simp [Invocation.finish?] at ran
  | faulted heap stack error =>
    simp only [Invocation.finish?, Option.some.injEq] at ran
    subst observation
    exact .fault destination heap stack error
  | finished heap result =>
    cases result with
    | error error =>
      simp only [Invocation.finish?, Option.some.injEq] at ran
      subst observation
      exact .raised destination heap error
    | ok value =>
      cases destination with
      | discard =>
        simp only [Invocation.finish?, Option.some.injEq] at ran
        subst observation
        exact .discarded heap value
      | bindGlobal name =>
        simp only [Invocation.finish?, Option.some.injEq] at ran
        subst observation
        exact .assigned heap name value
      | «assert» =>
        cases tested : truth value heap with
        | false =>
          simp [Invocation.finish?, tested] at ran
          subst observation
          exact .assertFalse heap value tested
        | true =>
          simp [Invocation.finish?, tested] at ran
          subst observation
          exact .assertTrue heap value tested

private theorem of_settles {globals : Executor.GlobalLookup} {destination : Destination}
    {state : Executor.State} {lists : Silmaril.Languages.Python.Core.Module.ListHeap} {observation : Observation}
    (delivered : Settles globals lists destination state observation) :
    (Invocation.mkWithLists globals destination state lists).finish? = some observation := by
  cases delivered with
  | assertTrue heap value tested => simp [Invocation.finish?, tested]
  | assertFalse heap value tested => simp [Invocation.finish?, tested]
  | _ => rfl

theorem finish_iff {invocation : Invocation} {observation : Observation} :
    invocation.finish? = some observation ↔
      Settles invocation.globals invocation.lists invocation.destination invocation.state observation :=
  ⟨selected, of_settles⟩

end Silmaril.Proofs.Languages.Python.Core.Module.Functions
