module

public import Silmaril.Languages.Python.Core.Defs
public import Silmaril.Languages.Python.Source.Scope.Defs

/-! # Translation of one closed Python source function

The accepted module contains one undecorated, zero-argument function with a
single return of integer literals and exact addition. The target is the
body of that function, after entry. Source names and module loading have
their own semantics outside this translation.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closed

inductive Error where
  | scope (diagnostic : Source.Diagnostic)
  | moduleShape
  | expressionShape
  deriving BEq, DecidableEq, Repr

def lowerExpr : Source.Expr → Except Error Core.Expr
  | .integer value => .ok (.int value)
  | .binary .add left right =>
    (lowerExpr left).bind fun lhs => (lowerExpr right).map (.binary .add lhs)
  | _ => .error .expressionShape

def lower : Source.Module → Except Error Core.Body
  | ⟨[.functionDef _ [] [.return_ (some value)] [] none]⟩ =>
    (lowerExpr value).map Core.Body.mk
  | _ => .error .moduleShape

def compile (source : Source.Module) : Except Error Core.Body :=
  match Source.analyze source with
  | .error diagnostic => .error (.scope diagnostic)
  | .ok _ => lower source

inductive ExprTranslation : Source.Expr → Core.Expr → Prop where
  | integer (value : Int) : ExprTranslation (.integer value) (.int value)
  | add {left right : Source.Expr} {lhs rhs : Core.Expr}
      (leftTranslation : ExprTranslation left lhs) (rightTranslation : ExprTranslation right rhs) :
      ExprTranslation (.binary .add left right) (.binary .add lhs rhs)

inductive Translation : Source.Module → Core.Body → Prop where
  | function (name : Source.Name) {value : Source.Expr} {target : Core.Expr}
      (translated : ExprTranslation value target) :
      Translation ⟨[.functionDef name [] [.return_ (some value)] [] none]⟩ ⟨target⟩

/-- The module's outer syntax, before checking the returned expression. -/
def ModuleShape (source : Source.Module) : Prop :=
  ∃ name value, source = ⟨[.functionDef name [] [.return_ (some value)] [] none]⟩

/-- Independent conditions for the reported phase and cause of rejection. -/
def Rejection (source : Source.Module) : Error → Prop
  | .scope diagnostic => Source.analyze source = .error diagnostic
  | .moduleShape => (∃ scope, Source.analyze source = .ok scope) ∧ ¬ ModuleShape source
  | .expressionShape =>
    (∃ scope, Source.analyze source = .ok scope) ∧ ModuleShape source ∧
      ¬ ∃ target, Translation source target

inductive Evaluates : Source.Expr → Int → Prop where
  | integer (value : Int) : Evaluates (.integer value) value
  | add {left right : Source.Expr} {lhs rhs : Int}
      (leftEval : Evaluates left lhs) (rightEval : Evaluates right rhs) :
      Evaluates (.binary .add left right) (lhs + rhs)

inductive Returns : Source.Module → Int → Prop where
  | function (name : Source.Name) {value : Source.Expr} {result : Int}
      (evaluates : Evaluates value result) :
      Returns ⟨[.functionDef name [] [.return_ (some value)] [] none]⟩ result

end Silmaril.Languages.Python.Compile.Closed
