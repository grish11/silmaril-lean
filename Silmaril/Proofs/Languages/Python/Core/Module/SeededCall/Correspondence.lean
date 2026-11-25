module

public import Silmaril.Languages.Python.Core.Module.SeededCall.Defs

public section

namespace Silmaril.Proofs.Languages.Python.Core.Module.SeededCall

open Silmaril.Languages.Python.Core.Module.SeededCall

theorem delivers_iff {expectation : Expectation} {input output : Result} :
    expectation.deliver input = output ↔ Delivers expectation input output := by
  constructor
  · intro selected
    cases input with
    | ok value => exact selected ▸ Delivers.returned value
    | error failure =>
      cases failure with
      | unsupported => exact selected ▸ Delivers.unsupported
      | raised error =>
        by_cases accepted : expectation.expected.catches error.classify
        · simp [Expectation.deliver, accepted] at selected
          exact selected ▸ Delivers.caught error accepted
        · simp [Expectation.deliver, accepted] at selected
          exact selected ▸ Delivers.uncaught error accepted
  · intro delivered
    cases delivered with
    | returned | unsupported => rfl
    | caught error accepted => simp [Expectation.deliver, accepted]
    | uncaught error different => simp [Expectation.deliver, different]

private theorem unique {arity : Nat} {request : Request arity} {first second : Result}
    (left : Executes request first) (right : Executes request second) : first = second := by
  induction left generalizing second with
  | equal left right same =>
    cases right with
    | equal => rfl
    | unequal _ _ different => contradiction
  | unequal left right different =>
    cases right with
    | equal _ _ same => contradiction
    | unequal => rfl
  | expected callback handled ih =>
    cases right with
    | expected other delivered =>
      have equal := ih other
      calc
        _ = _ := (delivers_iff.mpr handled).symm
        _ = _ := equal ▸ delivers_iff.mpr delivered
  | nonCallable => cases right; rfl
  | unsupported => cases right; rfl

private theorem computed (callee : Value) (arguments : List Value) :
    Executes (Request.decode callee arguments) (invoke callee arguments) := by
  induction arguments using (measure (List.length : List Value → Nat)).wf.induction generalizing callee with
  | h arguments ih =>
    cases decoded : Request.decode callee arguments with
    | compare left right =>
      rw [invoke, decoded]
      by_cases same : left = right
      · simp [same]
        exact .equal _ _ rfl
      · simp [same]
        exact .unequal _ _ same
    | expect expectation callback operands shorter =>
      rw [invoke, decoded]
      exact .expected (ih operands shorter callback) (delivers_iff.mp rfl)
    | nonCallable =>
      rw [invoke, decoded]
      exact .nonCallable
    | unsupported =>
      rw [invoke, decoded]
      exact .unsupported

theorem invoke_iff {callee : Value} {arguments : List Value} {result : Result} :
    invoke callee arguments = result ↔ Executes (Request.decode callee arguments) result :=
  ⟨fun selected => selected ▸ computed callee arguments, unique (computed callee arguments)⟩

end Silmaril.Proofs.Languages.Python.Core.Module.SeededCall
