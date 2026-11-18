module

public import Silmaril.Cerberus.Elaboration.Arithmetic.Defs

/-! Integer bitwise equations from `frontend/model/translation.lem:607–658`
at Cerberus `b3e11ea334e95359907d4abf9194f0e7fedc6c6a`.
Four wrappers precede both child translations. Runtime arithmetic conversions,
standard annotations and the unspecified fallback are retained. CHERI rejects.
This is elaboration syntax, not a source-to-machine refinement theorem. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Bitwise
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

def operatorData : ArithmeticOperator → Except String (String × Ctor)
  | .band => .ok ("§6.5.10", .ivAnd)
  | .bxor => .ok ("§6.5.11", .ivXor)
  | .bor => .ok ("§6.5.12", .ivOr)
  | _ => .error "Translation.translate_bitwise_operator: expected AND, XOR or OR"

def translate (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (resultType leftType rightType : Ctype)
    (operator : ArithmeticOperator) (left right : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI bitwise elaboration")
  let (standard, constructor) ← Constants.liftResult (operatorData operator)
  let first ← State.wrappedFreshSymbol (.loaded .integer)
  let second ← State.wrappedFreshSymbol (.loaded .integer)
  let firstObject ← State.wrappedFreshSymbol (.object .integer)
  let secondObject ← State.wrappedFreshSymbol (.object .integer)
  let coreLeft ← left
  let coreRight ← right
  let promoted ← Constants.liftResult (Arithmetic.usualArithmetic config env bindings false
    leftType rightType firstObject.expression secondObject.expression)
  let (promotedLeft, promotedRight) := standardPair (standard ++ "#3") promoted
  let value : Pure := .mk [] () (.ctor constructor [ailCtype resultType, promotedLeft, promotedRight])
  let pattern ← Constants.liftResult (tuplePattern [first.pattern, second.pattern])
  let values ← Constants.liftResult (tuplePure [first.expression, second.expression])
  let specifiedPattern ← Constants.liftResult (tuplePattern
    [Construction.specifiedPattern firstObject.pattern, Construction.specifiedPattern secondObject.pattern])
  return addStandard standard (weakSequence pattern (unseq [coreLeft, coreRight])
    (pureEffect (casePure values
      [(specifiedPattern, specified (standardPure (standard ++ "#4") value)),
       (wildcard (.tuple [.loaded .integer, .loaded .integer]), unspecified resultType)])))

end Silmaril.Cerberus.Elaboration.Bitwise
