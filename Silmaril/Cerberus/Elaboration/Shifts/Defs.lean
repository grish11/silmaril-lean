module

public import Silmaril.Cerberus.Elaboration.Arithmetic.Defs

/-! Non-CHERI left shift from Cerberus b3e11ea334e95359907d4abf9194f0e7fedc6c6a,
`frontend/model/translation.lem:1661–1761`. Seven wrappers precede children;
actual runtime promotion/width/representability calls, UB and Driver/Cn branches
are retained. This defines elaboration syntax, not runtime adequacy. -/
@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Shifts
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

def left (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (location : Loc) (resultType leftType rightType : Ctype)
    (leftChild rightChild : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI left shift")
  let first ← State.wrappedFreshSymbol (.loaded .integer)
  let second ← State.wrappedFreshSymbol (.loaded .integer)
  let firstObject ← State.wrappedFreshSymbol (.object .integer)
  let secondObject ← State.wrappedFreshSymbol (.object .integer)
  let promotedFirst ← State.wrappedFreshSymbol (.object .integer)
  let promotedSecond ← State.wrappedFreshSymbol (.object .integer)
  let result ← State.wrappedFreshSymbol (.object .integer)
  let coreLeft ← leftChild
  let coreRight ← rightChild
  let some resultInteger := Arithmetic.integerType resultType
    | throw (.message "ill-typed Ail Shl: result must have integer type")
  let signed ← Constants.liftResult (Constants.targetResult (Target.signedness config env resultInteger))
  let (_, leftInteger) ← Constants.liftResult (Arithmetic.promoteType config env leftType)
  let (_, rightInteger) ← Constants.liftResult (Arithmetic.promoteType config env rightType)
  let leftPromotion ← Constants.liftResult (Arithmetic.convert bindings false leftInteger firstObject.expression)
  let rightPromotion ← Constants.liftResult (Arithmetic.convert bindings false rightInteger secondObject.expression)
  let width ← Constants.liftResult (Runtime.standardCall bindings "ctype_width" [ailCtype resultType])
  let width := annotateInteger rightInteger width
  let power := operation .exp (integer 2) promotedSecond.expression
  let product := operation .mul promotedFirst.expression power
  let backend := (← get).backend
  let representable ← if signed && backend != "Cn" then
    Constants.liftResult (Runtime.standardCall bindings "is_representable_integer"
      [result.expression, ailCtype resultType])
    else pure (boolean false)
  let shifted := if signed then
    standardPure "§6.5.7#4, sentence 3"
      (ifPure (operation .lt promotedFirst.expression (integer 0))
        (standardUndefined location "§6.5.7#3, sentence 3" .UB052a_negative_left_shift)
        (if backend == "Cn" then specified
          (catchExceptionalCondition resultInteger .shl promotedFirst.expression promotedSecond.expression)
         else letPure result.pattern product (ifPure representable (specified result.expression)
          (standardUndefined location "§6.5.7#3, sentence 3" .UB052b_non_representable_left_shift))))
    else if backend == "Cn" then specified
      (wrapInteger resultInteger .shl promotedFirst.expression promotedSecond.expression)
    else specified (standardPure "§6.5.7#4, sentence 2"
      (operation .remT product (operation .add (ivmax (ailCtype resultType)) (integer 1))))
  let checked := ifPure (operation .lt promotedSecond.expression (integer 0))
    (standardUndefined location "§6.5.7#3, sentence 3" .UB051a_negative_shift)
    (ifPure (operation .or (operation .lt width promotedSecond.expression)
        (operation .eq width promotedSecond.expression))
      (standardUndefined location "§6.5.7#4, sentence 3" .UB51b_shift_too_large) shifted)
  let promoted := letPure promotedFirst.pattern (standardPure "§6.5.7#3, sentence 1" leftPromotion)
    (letPure promotedSecond.pattern (standardPure "§6.5.7#3, sentence 1" rightPromotion) checked)
  let inputPattern ← Constants.liftResult (tuplePattern [first.pattern, second.pattern])
  let inputs ← Constants.liftResult (tuplePure [first.expression, second.expression])
  let unspecifiedRight ← Constants.liftResult (tuplePattern
    [wildcard (.loaded .integer), unspecifiedPattern (wildcard .ctype)])
  let unspecifiedLeft ← Constants.liftResult (tuplePattern
    [unspecifiedPattern (wildcard .ctype), wildcard (.loaded .integer)])
  let bothSpecified ← Constants.liftResult (tuplePattern
    [specifiedPattern firstObject.pattern, specifiedPattern secondObject.pattern])
  return addStandard "§6.5.7" (weakSequence inputPattern (unseq [coreLeft, coreRight])
    (pureEffect (casePure inputs
      [(unspecifiedRight, standardUndefined location "§6.5#5" .UB036_exceptional_condition),
       (unspecifiedLeft, if signed then standardUndefined location "§6.5#5" .UB036_exceptional_condition else unspecified resultType),
       (bothSpecified, promoted)])))
end Silmaril.Cerberus.Elaboration.Shifts
