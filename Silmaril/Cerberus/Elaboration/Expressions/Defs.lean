module

public import Silmaril.Cerberus.Elaboration.Arithmetic.Defs
public import Silmaril.Cerberus.Elaboration.Bitwise.Defs
public import Silmaril.Cerberus.Elaboration.Members.Defs
public import Silmaril.Cerberus.Elaboration.Shifts.Defs
public import Silmaril.Cerberus.Elaboration.ObjectExpressions.Defs
public import Silmaril.Cerberus.Elaboration.Comparisons.Defs
public import Silmaril.Cerberus.Elaboration.Designators.Defs
public import Silmaril.Cerberus.Elaboration.Calls.Defs
public import Silmaril.Cerberus.Elaboration.CallArguments.Defs
public import Silmaril.Cerberus.Elaboration.NullPointers.Defs
public import Silmaril.Cerberus.Elaboration.IntegerCasts.Defs
public import Silmaril.Cerberus.Elaboration.Conditionals.Defs

/-! Actual typed-Ail expression dispatcher for constants, object
identifiers/rvalues, scalar add/sub/mul and AND/XOR/OR, pointer-member addresses, scalar lt/le/gt/ge/eq/ne, integer conditionals and short-circuit operators, direct integer casts, integer-zero pointer casts and normal fixed-integer direct calls.
The frozen constant port remains independently usable. Recursive effects,
marker freshness, full-expression bounds and annotation order are retained.
Other expression forms and expression-result lifetimes outside the call helper
reject explicitly. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Expressions
open Silmaril.Cerberus
open Construction

/-- Shared outer annotation order from `translation.lem:1500`.
The call branch attaches its computed standard annotations at `ccall`;
this outer wrapper does not attach that list to every expression form. -/
def annotate (category : Ail.GenTypeCategory) (location : Loc) (type : Ctype)
    (expression : Effect) : Effect :=
  let typed := match category with
    | .lvalue .. => expression
    | .rvalue _ => Constants.annotateIntegerEffect type expression
  addLocation location (addExpression typed)

/-- Actual integer TestEq/TestNe syntax, retaining operand annotations/location. -/
def integerTestInput (equal : Bool) (config : Target.Config) (env : Target.Environment)
    (input : Ail.TypedExpression) : Except String Ail.TypedExpression := do
  let test ← ControlTests.equalZero config env input
  let .mk category annotations location (.binary left _ right) := test
    | throw "internal: integer test is not binary"
  return .mk category annotations location (.binary left (if equal then .eq else .ne) right)

/-- Elaborate the synthesized test without recursively expanding the input AST.
The callback is the actual operand translation; the octal-zero child uses the
constant translator. Synthetic outer marker allocation and annotation order
match the ordinary binary expression dispatcher. -/
def integerTest (equal : Bool) (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (input : Ail.TypedExpression)
    (child : State.ElabM Effect) : State.ElabM Effect := do
  let test ← Constants.liftResult (integerTestInput equal config env input)
  let .mk category annotations location (.binary _ _ zero) := test
    | throw (.message "internal: integer test is not binary")
  let resultType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env test))
  let operandType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env input))
  match ← Constants.liftResult (Constants.marker annotations) with
  | some _ => let _ ← State.recordObjectTypesMarker; pure ()
  | none => pure ()
  let core ← if equal then
      Comparisons.equal config env bindings resultType operandType operandType child
        (Constants.expression config env zero)
    else
      Comparisons.notEqual config env bindings resultType operandType operandType child
        (Constants.expression config env zero)
  return annotate category location resultType core

def logicalLiteral (value : Int) (basis : Ail.Basis) : Ail.TypedExpression :=
  .mk ControlTests.signedIntCategory [] .unknown (.const (.integer (.iconstant value basis none)))

/-- Integer &&/|| follow the pinned typed-Ail conditional desugaring, including
its nested equality tests and synthetic expression annotations. Core retains
strong sequencing and evaluates only the selected RHS branch. -/
def logical (conjunction : Bool) (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (location : Loc) (left right : Ail.TypedExpression)
    (coreLeft coreRight : State.ElabM Effect) : State.ElabM Effect := do
  let leftTest ← Constants.liftResult (integerTestInput true config env left)
  let rightTest ← Constants.liftResult (integerTestInput false config env right)
  let zero := logicalLiteral 0 .octal
  let one := logicalLiteral 1 .decimal
  let yes := if conjunction then zero else rightTest
  let no := if conjunction then rightTest else one
  let conditional := Ail.Expression.mk ControlTests.signedIntCategory [] location
    (.cond leftTest (some yes) no)
  let resultType ← Constants.liftResult
    (Constants.targetResult (GeneralizedTypes.expressionType config env conditional))
  let yesType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env yes))
  let noType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env no))
  let test := integerTest true config env bindings leftTest
    (integerTest true config env bindings left coreLeft)
  let rhs := integerTest false config env bindings right coreRight
  let coreYes := if conjunction then Constants.expression config env zero else rhs
  let coreNo := if conjunction then rhs else Constants.expression config env one
  let core ← Conditionals.translate true bindings location resultType yesType noType test coreYes coreNo
  let standards := if conjunction then ["6.5.13#3", "6.5.13#4"] else ["6.5.14#3", "6.5.14#4"]
  return addStandards standards (annotate ControlTests.signedIntCategory location resultType core)

def expression (config : Target.Config) (env : Target.Environment) (bindings : List Runtime.Binding)
    (input : Ail.TypedExpression) (aliases : Designators.Aliases := []) : State.ElabM Effect :=
  match input with
  | .mk _ _ _ (.const _) => Constants.expression config env input
  | .mk category annotations location node => do
      let type ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env input))
      if Constants.isPointer type && NullPointers.isNullPointerConstant input then
        return pureEffect (specified (nullptr type))
      let standardAnnotations ← match ← Constants.liftResult (Constants.marker annotations) with
        | some _ => do
            let marker ← State.recordObjectTypesMarker
            pure (.markerObjectTypes marker :: annotations)
        | none => pure annotations
      let core ← match _hnode : node with
        | .memberofptr pointer member => do
            let pointerType ← Constants.liftResult
              (Constants.targetResult (GeneralizedTypes.expressionType config env pointer))
            Members.pointerMember config.cheri config.strictPointerArithmetic location pointerType member
              (expression config env bindings pointer aliases)
        | .binary left operator right => do
            let leftType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env left))
            let rightType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env right))
            match operator with
            | .arithmetic arithmetic =>
                if arithmetic == .band || arithmetic == .bxor || arithmetic == .bor then
                  Bitwise.translate config env bindings type leftType rightType arithmetic
                    (expression config env bindings left aliases) (expression config env bindings right aliases)
                else if arithmetic == .shl then
                  Shifts.left config env bindings location type leftType rightType
                    (expression config env bindings left aliases) (expression config env bindings right aliases)
                else
                  Arithmetic.translate config env bindings location type leftType rightType arithmetic
                    (expression config env bindings left aliases) (expression config env bindings right aliases)
            | .gt =>
                Comparisons.greater config env bindings type leftType rightType
                  (expression config env bindings left aliases) (expression config env bindings right aliases)
            | .lt =>
                Comparisons.relational .less config env bindings type leftType rightType
                  (expression config env bindings left aliases) (expression config env bindings right aliases)
            | .le =>
                Comparisons.relational .lessEqual config env bindings type leftType rightType
                  (expression config env bindings left aliases) (expression config env bindings right aliases)
            | .ge =>
                Comparisons.relational .greaterEqual config env bindings type leftType rightType
                  (expression config env bindings left aliases) (expression config env bindings right aliases)
            | .eq =>
                if NullPointers.isNullPointerConstant left && Constants.isPointer rightType then
                  NullPointers.compareNull config false location rightType
                    (expression config env bindings right aliases)
                else if Constants.isPointer leftType && NullPointers.isNullPointerConstant right then
                  NullPointers.compareNull config false location leftType
                    (expression config env bindings left aliases)
                else
                  Comparisons.equal config env bindings type leftType rightType
                    (expression config env bindings left aliases) (expression config env bindings right aliases)
            | .ne =>
                if NullPointers.isNullPointerConstant left && Constants.isPointer rightType then
                  NullPointers.compareNull config true location rightType
                    (expression config env bindings right aliases)
                else if Constants.isPointer leftType && NullPointers.isNullPointerConstant right then
                  NullPointers.compareNull config true location leftType
                    (expression config env bindings left aliases)
                else
                  Comparisons.notEqual config env bindings type leftType rightType
                    (expression config env bindings left aliases) (expression config env bindings right aliases)
            | .and =>
                logical true config env bindings location left right
                  (expression config env bindings left aliases) (expression config env bindings right aliases)
            | .or =>
                logical false config env bindings location left right
                  (expression config env bindings left aliases) (expression config env bindings right aliases)
            | _ => throw (.message "unsupported: binary operator outside scalar add/sub/mul/lt/le/gt/ge/eq/ne/and/or")
        | .cond condition (some yes) no => do
            let yesType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env yes))
            let noType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env no))
            Conditionals.translate false bindings location type yesType noType
              (integerTest true config env bindings condition (expression config env bindings condition aliases))
              (expression config env bindings yes aliases) (expression config env bindings no aliases)
        | .cast _ destination operand => do
            let source ← Constants.liftResult
              (Constants.targetResult (GeneralizedTypes.expressionType config env operand))
            match destination with
            | .mk _ (.basic (.integer _)) =>
                IntegerCasts.translate config bindings source destination
                  (expression config env bindings operand aliases)
            | _ =>
                NullPointers.castInteger config source destination operand
                  (expression config env bindings operand aliases)
        | .ident symbol => ObjectExpressions.identifier config symbol
        | .rvalue child => do
            let childType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env child))
            ObjectExpressions.rvalue config location childType (expression config env bindings child aliases)
        | .functionDecay child => do
            let childType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env child))
            Designators.direct config aliases childType child
        | .call designator [] => do
            let designatorType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env designator))
            Calls.zeroArguments bindings location standardAnnotations designatorType
              (expression config env bindings designator aliases)
        | .call designator arguments => do
            let designatorType ← Constants.liftResult
              (Constants.targetResult (GeneralizedTypes.expressionType config env designator))
            let actuals ← arguments.attach.mapM fun argument => do
              let type ← Constants.liftResult
                (Constants.targetResult (GeneralizedTypes.expressionType config env argument.val))
              let .mk _ _ location _ := argument.val
              pure (CallArguments.Argument.mk location type
                (expression config env bindings argument.val aliases))
            CallArguments.translate config bindings location standardAnnotations designatorType
              (expression config env bindings designator aliases) actuals
        | _ => throw (.message "unsupported: actual expression form is outside supported scalar/object operations, integer conditionals and normal fixed-integer direct calls")
      return annotate category location type core
termination_by sizeOf input
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have memberBound := List.sizeOf_lt_of_mem argument.property
      omega

def wrappedExpression (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (input : Ail.TypedExpression)
    (aliases : Designators.Aliases := []) : State.ElabM Effect := do
  let (temporaries, core) ← State.trackTemporaryObjects (expression config env bindings input aliases)
  match temporaries with
  | [] => return .mk [.std "§6.5#2"] (.bound core)
  | _ => throw (.message "unsupported: expression temporary-object lifetimes are not ported")

end Silmaril.Cerberus.Elaboration.Expressions
