module
public import Silmaril.Cerberus.Elaboration.Arithmetic.Defs
public import Silmaril.Cerberus.Elaboration.MemoryActions.Defs
/-! Direct non-atomic integer postfix update, pinned translation.lem:663–773
and core_aux.lem:540–553 at b3e11ea334e95359907d4abf9194f0e7fedc6c6a.
CHERI, pointer/floating increments and atomic operands reject.
This constructs the actual SeqRMW/update expression, not an observed result. -/
@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Postfix
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

def translate (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (location : Loc) (resultType operandType : Ctype)
    (decrement : Bool) (child : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI postfix")
  let .mk _ (.basic (.integer _)) := operandType
    | throw (.message "unsupported: postfix operand is not a direct integer")
  let paragraph := if decrement then "#3" else "#2"
  let sentence := fun (n : Nat) => "§6.5.2.4" ++ paragraph ++ ", sentence " ++ toString n
  let pointer ← State.wrappedFreshSymbol (.object .pointer)
  let loaded ← State.wrappedFreshSymbol (.loaded .integer)
  let object ← State.wrappedFreshSymbol (.object .integer)
  let core ← child
  let (promotedType, _) ← Constants.liftResult (Arithmetic.promoteType config env operandType)
  let promoted ← Constants.liftResult (Runtime.standardCall bindings "conv_int" [ailCtype promotedType, object.expression])
  let raw := operation (if decrement then .sub else .add) object.expression (integer 1)
  let checked ← Constants.liftResult (Arithmetic.withIntegerBehavior config env promotedType
    (if decrement then .sub else .add) promoted (maybeAnnotateInteger promotedType (integer 1)) raw)
  let converted ← Constants.liftResult (Runtime.standardCall bindings "conv_int" [ailCtype resultType, checked])
  let update := casePure loaded.expression
    [(specifiedPattern object.pattern, specified (standardPure (sentence 2) converted)),
     (unspecifiedPattern (wildcard .ctype), unspecified operandType)]
  let type := ailCtype operandType
  let backend := (← get).backend
  let action := if backend == "Cn" || backend == "Bmc" then
      weakSequence loaded.pattern (MemoryActions.load location type pointer.expression .na)
        (weakSequence (wildcard .unit)
          (MemoryActions.store location false type pointer.expression update .na)
          (pureEffect loaded.expression))
    else MemoryActions.positive location (.seqRmw false type pointer.expression loaded.symbol update)
  return addStandards ["§6.5.2.4", sentence 1, sentence 3]
    (weakSequence pointer.pattern core action)
end Silmaril.Cerberus.Elaboration.Postfix
