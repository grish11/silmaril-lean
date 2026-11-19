module

public import Silmaril.Cerberus.Elaboration.Constants.Defs
public import Silmaril.Cerberus.Frontend.Desugar.Predicates.Defs

/-! Pinned null-pointer predicates and the integer-zero pointer cast branch of
translation.lem:1862-1884. Both unused wrappers and the final unused let symbol
are allocated, and the child is translated, even though its Core is discarded.
Other casts remain outside this selected non-CHERI source domain. -/
@[expose] public section
namespace Silmaril.Cerberus.Elaboration.NullPointers
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

def isNullPointerConstant (input : Ail.TypedExpression) : Bool :=
  Silmaril.Cerberus.Frontend.Desugar.isNullPointerConstant input

/-- The selected global non-fast-path initializer is a pointer cast of a direct
integer constant zero. A cast to int-pointer is not itself a null pointer constant. -/
def integerNullCast : Ail.TypedExpression → Bool
  | .mk _ _ _ (.cast _ (.mk _ (.pointer _ _))
      (.mk _ _ _ (.const (.integer (.iconstant number _ _))))) => decide (number = 0)
  | _ => false

/-- Actual cast branch with its source allocation and recursive-child order.
The resulting null value stores the referenced CType, as upstream does here. -/
def castInteger (config : Target.Config) (source destination : Ctype)
    (operand : Ail.TypedExpression) (child : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI pointer cast elaboration")
  let .mk _ (.basic (.integer _)) := source
    | throw (.message "unsupported: pointer-null cast source is not a direct integer")
  let .mk _ (.pointer _ referenced) := destination
    | throw (.message "unsupported: pointer-null cast destination is not a pointer")
  unless isNullPointerConstant operand do
    throw (.message "unsupported: pointer cast operand is not a null pointer constant")
  let _ ← State.wrappedFreshSymbol (.loaded .integer)
  let _ ← State.wrappedFreshSymbol (.object .integer)
  let _ ← child
  let _ ← State.freshDescription .none
  return addStandard "§6.5.4" (pureEffect (specified (nullptr referenced)))

/-- Null-constant equality branch from pinned `translation.lem:514–546`.
Only the pointer child is translated, before the three fresh wrappers. The
unspecified-loaded-value case retains the source UB instead of returning false.
General pointer/pointer comparisons and CHERI remain outside this slice. -/
def compareNull (config : Target.Config) (notEqual : Bool) (location : Loc)
    (pointerType : Ctype) (child : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI null-pointer comparison")
  unless Constants.isPointer pointerType do
    throw (.message "unsupported: null comparison requires a pointer operand")
  let core ← child
  let loaded ← State.wrappedFreshSymbol (.loaded .pointer)
  let object ← State.wrappedFreshSymbol (.object .pointer)
  let result ← State.wrappedFreshSymbol .boolean
  let nullValue := standardPure "§6.5.9#5, sentence 2" (nullptr pointerType)
  let operation := memoryOperation (if notEqual then .ptrNe else .ptrEq)
    [object.expression, nullValue]
  let yes := addStandard "§6.5.9#3" (pureEffect
    (ifPure result.expression (specified (integer 1)) (specified (integer 0))))
  return weakSequence loaded.pattern core (caseEffect loaded.expression
    [(specifiedPattern object.pattern, weakSequence result.pattern operation yes),
     (wildcard (.loaded .pointer), pureEffect
       (undefined location (.UB_CERB004_unspecified .UB_unspec_equality_ptr_vs_NULL)))])

end Silmaril.Cerberus.Elaboration.NullPointers
