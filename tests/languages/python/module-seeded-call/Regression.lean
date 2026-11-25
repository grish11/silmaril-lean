module

import Silmaril.Languages.Python.Core.Module.SeededCall.Thms

open Silmaril.Languages.Python.Core.Module.SeededCall

private def stockSubset : Bindings := [("AssertionError", .exceptionClass .assertionError)]

private def helpers (onReturn : AssertionArgument) : Bindings :=
  [("___assertRaises", .helper (.assertRaises onReturn)), ("___assertEqual", .helper .assertEqual)]

private def builtinSeed : Namespace := ⟨[], helpers .empty ++ stockSubset⟩
private def preambleSeed : Namespace :=
  ⟨helpers (.text "did not raise exception"), stockSubset⟩

private def emptyLocals : Locals 0 := #v[]

private def assertionCase (space : Namespace) : Result :=
  run space emptyLocals (.global "___assertRaises")
    [.global "AssertionError", .global "___assertEqual", .literal (.int 1), .literal (.int 2)]

private theorem caughtIntegerInequality (onReturn : AssertionArgument) :
    invoke (.helper (.assertRaises onReturn))
      [.exceptionClass .assertionError, .helper .assertEqual, .int 1, .int 2] = .ok .none := by
  simp [invoke.eq_def, Request.decode, Expectation.deliver, Raised.classify, ExceptionClass.catches]

-- Each seed is supplied explicitly. The stock subset includes only the class.
example : assertionCase Namespace.empty = .error (.raised (.runtime (.nameError "___assertRaises"))) := rfl
example : assertionCase ⟨[], stockSubset⟩ = .error (.raised (.runtime (.nameError "___assertRaises"))) := rfl
example : assertionCase builtinSeed = .ok .none := caughtIntegerInequality .empty
example : assertionCase preambleSeed = .ok .none := caughtIntegerInequality (.text "did not raise exception")

example : lookupBinding builtinSeed.moduleGlobals "___assertRaises" = none := rfl
example : lookupBinding preambleSeed.builtins "___assertRaises" = none := rfl
example : (builtinSeed.bindGlobal "___assertRaises" .none).lookupGlobal "___assertRaises" = some .none := rfl

private def localSlot : Fin 1 := ⟨0, by decide⟩
private def populated : Locals 1 := #v[some (.int 42)]
private def unbound : Locals 1 := #v[none]

example : (Operand.local localSlot).eval builtinSeed populated = .ok (.int 42) := rfl
example : (Operand.local localSlot).eval builtinSeed unbound = .error (.raised (.runtime (.unboundLocal 0))) := rfl
example : (Operand.global "AssertionError").eval builtinSeed populated = .ok (.exceptionClass .assertionError) := rfl

private def outerOnly : Namespace := ⟨[], [("___assertRaises", .helper (.assertRaises .empty))]⟩
example : assertionCase outerOnly = .error (.raised (.runtime (.nameError "AssertionError"))) := rfl
example : assertionCase ⟨[], outerOnly.builtins ++ stockSubset⟩ =
    .error (.raised (.runtime (.nameError "___assertEqual"))) := rfl

-- An alias still selects the closed descriptor and evaluates the supplied values.
example : run (Namespace.empty.bindGlobal "alias" (.helper .assertEqual)) emptyLocals (.global "alias")
    [.literal (.int (-5)), .literal (.int 8)] =
      .error (.raised (.assertionError (.integerPair (-5) 8))) := by
  change invoke (.helper .assertEqual) [.int (-5), .int 8] = _
  simp [invoke.eq_def, Request.decode]

example : invoke (.helper (.assertRaises .empty))
    [.exceptionClass .typeError, .helper .assertEqual, .int (-5), .int 8] =
      .error (.raised (.assertionError (.integerPair (-5) 8))) := by
  simp [invoke.eq_def, Request.decode, Expectation.deliver, Raised.classify, ExceptionClass.catches]

example : invoke (.helper (.assertRaises .empty)) [.exceptionClass .typeError, .none] = .ok .none := by
  simp [invoke.eq_def, Request.decode, Expectation.deliver, Raised.classify, ExceptionClass.catches]

example : invoke (.helper (.assertRaises .empty))
    [.exceptionClass .assertionError, .helper .assertEqual, .int 8, .int 8] =
      .error (.raised (.assertionError .empty)) := by
  simp [invoke.eq_def, Request.decode, Expectation.deliver]
example : invoke (.helper (.assertRaises (.text "did not raise exception")))
    [.exceptionClass .assertionError, .helper .assertEqual, .int 8, .int 8] =
      .error (.raised (.assertionError (.text "did not raise exception"))) := by
  simp [invoke.eq_def, Request.decode, Expectation.deliver]

-- The slice cannot construct exception objects or compare arbitrary objects.
example : invoke (.exceptionClass .assertionError) [] = .error .unsupported := by
  simp [invoke.eq_def, Request.decode]
example : invoke (.helper .assertEqual) [.none, .none] = .error .unsupported := by
  simp [invoke.eq_def, Request.decode]
example : invoke (.helper (.assertRaises .empty))
    [.exceptionClass .assertionError, .exceptionClass .assertionError] = .error .unsupported := by
  simp [invoke.eq_def, Request.decode, Expectation.deliver]
example : run builtinSeed populated (.global "___assertEqual") [.unsupported, .literal (.int 2)] =
    .error .unsupported := rfl

#print axioms Namespace.module_precedes
#print axioms Namespace.builtin_fallback
#print axioms Operand.eval_local
#print axioms Expectation.delivers_iff
#print axioms invoke_iff
