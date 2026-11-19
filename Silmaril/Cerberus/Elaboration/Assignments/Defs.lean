module
public import Silmaril.Cerberus.Elaboration.Arithmetic.Defs
public import Silmaril.Cerberus.Elaboration.Conversion.Defs
public import Silmaril.Cerberus.Elaboration.MemoryActions.Defs
public import Silmaril.Cerberus.Elaboration.NullPointers.Defs
/-! Non-CHERI direct arithmetic and pointer assignment equations from pinned
Cerberus b3e11ea translation.lem:2404–2499. Evaluation remains unsequenced,
the store is a negative action, and result/standard annotations are retained.
Atomic, aggregate and pointer-to-Bool branches reject. Upstream does not check
non-exact overlapping assignment UB here; no stronger adequacy is claimed. -/
@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Assignments
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

def translate (config : Target.Config) (bindings : List Runtime.Binding)
    (location : Loc) (leftType rightType : Ctype) (rightInput : Ail.TypedExpression)
    (left right : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI assignment")
  let pointer ← State.wrappedFreshSymbol (.object .pointer)
  let lhs ← left
  let (objectType, rhs, convert) ← match leftType with
    | .mk _ (.pointer _ referenced) => do
        let rhs ← right
        if NullPointers.isNullPointerConstant rightInput then
          pure (.pointer, pureEffect (specified (nullptr referenced)), fun x => Except.ok x)
        else
          unless Constants.isPointer rightType do
            throw (.message "unsupported: pointer assignment source")
          pure (.pointer, rhs, fun x => Except.ok x)
    | .mk _ (.basic (.integer _)) | .mk _ (.basic (.floating _)) => do
        let rhs ← right
        let objectType ← Constants.liftResult (Arithmetic.scalarObjectType rightType)
        pure (objectType, rhs, Conversion.loadedArithmetic bindings rightType leftType)
    | _ => throw (.message "unsupported: atomic or aggregate assignment")
  let value ← State.wrappedFreshSymbol (.loaded objectType)
  let object := standardPure "§6.5.16#3, sentence 1" pointer.expression
  let converted ← Constants.liftResult (convert value.expression)
  let stored := standardPure "§6.5.16.1#2, conversion" converted
  let patterns ← Constants.liftResult (tuplePattern [pointer.pattern, value.pattern])
  let store : Effect := .mk [.std "§6.5.16.1#2, store"]
    (.action (.mk .neg (.mk location () (.store false (ailCtype leftType) object stored .na))))
  return addStandard "§6.5.16#3, sentence 4"
    (weakSequence patterns (addStandard "§6.5.16#3, sentence 5" (unseq [lhs, rhs]))
      (weakSequence (wildcard .unit) store (pureEffect stored)))
end Silmaril.Cerberus.Elaboration.Assignments
