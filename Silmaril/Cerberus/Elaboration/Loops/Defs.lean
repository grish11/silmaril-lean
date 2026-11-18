module

public import Silmaril.Cerberus.Elaboration.ControlFlow.Defs
public import Silmaril.Cerberus.Elaboration.Lifetimes.Defs

/-! Actual integer while lowering from pinned `translation.lem:3800–3841`.
The statement dispatcher owns eager loop-symbol/Boolean allocation and source
wrappers. This constructor preserves visible-object arguments, Core loop
annotations and nondeterministic unspecified conditions. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Loops
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

def arguments (visible : List Lifetimes.Visible) : List SaveArgument :=
  visible.map fun (symbol, type) =>
    (symbol, ((.object .pointer, some (type, .pointer)), symbolPure symbol))

def integerWhile (config : Target.Config) (types : Target.Environment)
    (loopSymbol : Sym) (prepared : State.WrappedSymbol) (location : Loc)
    (condition : Ail.TypedExpression) (loopId : Nat)
    (wrappedCondition : Loc → Ail.TypedExpression → State.ElabM Effect)
    (body : State.ElabM Effect) : State.ElabM Effect := do
  let binders ← ControlFlow.freshBinders
  let test ← Constants.liftResult (ControlTests.equalZero config types condition)
  let coreTest ← wrappedCondition location test
  let coreBody ← body
  let visible ← Lifetimes.captureVisible
  let repeatBody := strongSequence (wildcard .unit) coreBody
    (Construction.run loopSymbol (visible.map fun entry => symbolPure entry.1))
  return saveWith [.label (.loop loopId)] (loopSymbol, .unit) (arguments visible)
    (ControlFlow.finish prepared binders coreTest repeatBody skip)

end Silmaril.Cerberus.Elaboration.Loops
