module

public import Init

/-! # Python source syntax for module, function and class scope

This fragment starts at constructor data. Names have no resolved access
annotations. Parameter syntax retains its kind, default and optional annotation.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Source

abbrev Name := String

inductive BinaryOperator where
  | add | sub | mul | trueDiv | floorDiv | modulo | pow | matrixMul
  | bitAnd | bitOr | bitXor | shiftLeft | shiftRight
  deriving Repr

inductive UnaryOperator where
  | positive | negative | invert | not_
  deriving Repr

inductive BooleanOperator where
  | and_ | or_
  deriving Repr

inductive Comparison where
  | eq | ne | lt | le | gt | ge | is_ | isNot | in_ | notIn
  deriving Repr

inductive UnsupportedExpr where
  | listComprehension | setComprehension | dictComprehension | generatorExpression | bytesLiteral
  deriving BEq, DecidableEq, Repr

inductive ArgumentKind where
  | positional | keyword (name : Name) | unpackIterable | unpackMapping
  deriving Repr

inductive ParameterKind where
  | positionalOnly | positionalOrKeyword | varPositional | keywordOnly | varKeyword
  deriving Repr

mutual
  inductive Expr where
    | name (identifier : Name)
    | integer (value : Int)
    | floatBits (bits : UInt64)
    | text (codepoints : List UInt32)
    | boolean (value : Bool)
    | none_
    | ellipsis
    | list_ (elements : List Expr)
    | tuple (elements : List Expr)
    | dictionary (entries : List (Option Expr × Expr))
    | unary (operator : UnaryOperator) (operand : Expr)
    | binary (operator : BinaryOperator) (left right : Expr)
    | booleanOp (operator : BooleanOperator) (operands : List Expr)
    | conditional (condition consequent alternate : Expr)
    | comparison (left : Expr) (rest : List (Comparison × Expr))
    | call (callee : Expr) (arguments : List Expr)
    | callWith (callee : Expr) (arguments : List (ArgumentKind × Expr))
    | starred (value : Expr)
    | attribute (receiver : Expr) (field : Name)
    | subscript (receiver index : Expr)
    | slice (receiver : Expr) (lower upper stride : Option Expr)
    | yield_ (value : Option Expr)
    | lambda (parameters : List Parameter) (body : Expr)
    | unsupported (form : UnsupportedExpr)
    deriving Repr

  structure Parameter where
    name : Name
    defaultValue : Option Expr := none
    kind : ParameterKind := .positionalOrKeyword
    annotation : Option Expr := none
    deriving Repr
end

inductive Target where
  | name (identifier : Name)
  | attribute (receiver : Expr) (field : Name)
  | subscript (receiver index : Expr)
  | tuple (elements : List Target)
  | list_ (elements : List Target)
  deriving Repr

structure ImportName where
  member : Name
  alias : Option Name := none
  deriving Repr

mutual
  inductive Stmt where
    | assign (target : Name) (value : Expr)
    | assignTargets (targets : List Target) (value : Expr)
    | delete (target : Name)
    | deleteTargets (targets : List Target)
    | expression (value : Expr)
    | return_ (value : Option Expr)
    | raise_ (exception cause : Option Expr)
    | assert_ (condition : Expr) (message : Option Expr)
    | pass
    | break_
    | continue_
    | globalDecl (names : List Name)
    | nonlocalDecl (names : List Name)
    | if_ (condition : Expr) (body otherwise : List Stmt)
    | while_ (condition : Expr) (body otherwise : List Stmt)
    | for_ (target : Target) (iterator : Expr) (body otherwise : List Stmt)
    | try_ (body : List Stmt) (handlers : List ExceptHandler) (otherwise cleanup : List Stmt)
    | importFrom (modulePath : List Name) (level : Nat) (names : List ImportName)
    | functionDef (name : Name) (parameters : List Parameter) (body : List Stmt)
        (decorators : List Expr := []) (returnAnnotation : Option Expr := none)
    | classDef (name : Name) (bases : List Expr) (body : List Stmt)
        (decorators : List Expr := []) (keywords : List (Option Name × Expr) := [])
    deriving Repr

  structure ExceptHandler where
    condition : Option Expr
    target : Option Name
    body : List Stmt
    deriving Repr
end

structure Module where
  body : List Stmt
  deriving Repr

end Silmaril.Languages.Python.Source
