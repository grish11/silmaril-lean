module

public import Silmaril.Cerberus.GeneralizedTypes.Defs

/-! Integer/pointer TestEq synthesis from pinned `translation.lem:94-114`. This creates
actual typed-Ail syntax, retaining the original category on the octal-zero or
null child and copying annotations/location. Floating test synthesis
remains outside this focused helper, as do statement lowering and scheduling. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.ControlTests
open Silmaril.Cerberus

def signedIntCategory : Ail.GenTypeCategory :=
  .rvalue (.basic (.integer (.concrete (.signed .int))))

def integerType : Ctype → Bool
  | .mk _ (.basic (.integer _)) => true
  | _ => false

/-- Source `mkTestExpression TestEq e` in its integer and pointer domains. -/
def equalZero (config : Target.Config) (env : Target.Environment)
    (input : Ail.TypedExpression) : Except String Ail.TypedExpression := do
  let type ← (GeneralizedTypes.expressionType config env input).mapError reprStr
  let .mk category annotations location _ := input
  let constant ← if integerType type then
      pure (Ail.Constant.integer (.iconstant 0 .octal none))
    else match type with
      | .mk _ (.pointer ..) => pure Ail.Constant.null
      | _ => throw "unsupported: integer or pointer control test required"
  let zero := Ail.Expression.mk category annotations location
    (.const constant)
  return .mk signedIntCategory annotations location (.binary input .eq zero)

end Silmaril.Cerberus.Elaboration.ControlTests
