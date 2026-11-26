module

public import Silmaril.Languages.Python.Core.Module.SeededCall.Defs

public section

namespace Silmaril.Proofs.Languages.Python.Core.Module.SeededCall

open Silmaril.Languages.Python.Core.Module.SeededCall
open Silmaril.Languages.Python.Core.Module.TupleDispatch (equalContents)

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
  | equalNumeric left right same =>
    cases right with
    | equalNumeric => rfl
    | unequalNumeric _ _ different => contradiction
  | unequalNumeric left right different =>
    cases right with
    | equalNumeric _ _ same => contradiction
    | unequalNumeric => rfl
  | equalText left right same =>
    cases right with
    | equalText => rfl
    | unequalText _ _ different => contradiction
  | unequalText left right different =>
    cases right with
    | equalText _ _ same => contradiction
    | unequalText => rfl
  | equalTuple left right same =>
    cases right with
    | equalTuple => rfl
    | unequalTuple _ _ different => contradiction
  | unequalTuple left right different =>
    cases right with
    | equalTuple _ _ same => contradiction
    | unequalTuple => rfl
  | asserted | assertionFailed | textConversion | truthConversion | intFromBool | callable | isinstance | distinctIntBool | copyTuple | copyTupleObject => cases right; rfl
  | tupleAsserted | tupleAssertionFailed => cases right; rfl
  | listAsserted _ nonempty =>
    cases right with
    | listAsserted => rfl
    | listAssertionFailed _ empty => contradiction
  | listAssertionFailed _ empty =>
    cases right with
    | listAsserted _ nonempty => contradiction
    | listAssertionFailed => rfl
  | sameBool left right same =>
    cases right with
    | sameBool => rfl
    | distinctBool _ _ different => contradiction
  | distinctBool left right different =>
    cases right with
    | sameBool _ _ same => contradiction
    | distinctBool => rfl
  | expected callback handled ih =>
    cases right with
    | expected other delivered =>
      have equal := ih other
      calc
        _ = _ := (delivers_iff.mpr handled).symm
        _ = _ := equal ▸ delivers_iff.mpr delivered
  | emptyTuple => cases right; rfl
  | nonCallable => cases right; rfl
  | unsupported => cases right; rfl

private theorem computed (callee : Value) (arguments : List Value) :
    Executes (Request.decode callee arguments) (invoke callee arguments) := by
  induction arguments using (measure (List.length : List Value → Nat)).wf.induction generalizing callee with
  | h arguments ih =>
    cases decoded : Request.decode callee arguments with
    | assertBoolean value =>
      rw [invoke, decoded]
      cases value
      · exact .assertionFailed
      · exact .asserted
    | assertTuple nonempty =>
      rw [invoke, decoded]
      cases nonempty
      · exact .tupleAssertionFailed
      · exact .tupleAsserted
    | assertList object =>
      rw [invoke, decoded]
      change Executes (.assertList object)
        (if object.contents.isEmpty then .error (.raised (.assertionError (.listObject object))) else .ok .none)
      by_cases empty : object.contents.isEmpty = true
      · rw [ite_eq_left empty]
        exact .listAssertionFailed object empty
      · rw [ite_eq_right empty]
        exact .listAsserted object empty
    | compare left right =>
      rw [invoke, decoded]
      by_cases same : left = right
      · simp [same]
        exact .equal _ _ rfl
      · simp [same]
        exact .unequal _ _ same
    | compareNumeric left right =>
      rw [invoke, decoded]
      by_cases same : left.equal right = true
      · simp [same]
        exact .equalNumeric _ _ same
      · simp [same]
        exact .unequalNumeric _ _ same
    | compareText left right =>
      rw [invoke, decoded]
      by_cases same : left = right
      · simp [same]
        exact .equalText _ _ rfl
      · simp [same]
        exact .unequalText _ _ same
    | compareTuple left right =>
      rw [invoke, decoded]
      by_cases same : equalContents left right = true
      · simp [same]
        exact .equalTuple _ _ same
      · simp [same]
        exact .unequalTuple _ _ same
    | textConversion value =>
      rw [invoke, decoded]
      exact .textConversion value
    | truthConversion value =>
      rw [invoke, decoded]
      exact .truthConversion value
    | intFromBool value =>
      rw [invoke, decoded]
      exact .intFromBool value
    | callable probe =>
      rw [invoke, decoded]
      exact .callable probe
    | isinstance probe =>
      rw [invoke, decoded]
      exact .isinstance probe
    | boolIdentity left right =>
      rw [invoke, decoded]
      by_cases same : BoolIdentity.ofBool left = BoolIdentity.ofBool right
      · simp [same]
        exact .sameBool _ _ same
      · simp [same]
        exact .distinctBool _ _ same
    | distinctIntBool =>
      rw [invoke, decoded]
      exact .distinctIntBool
    | emptyTuple =>
      rw [invoke, decoded]
      exact .emptyTuple
    | copyTuple items =>
      rw [invoke, decoded]
      exact .copyTuple items
    | copyTupleObject object =>
      rw [invoke, decoded]
      exact .copyTupleObject object
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
