module

public import Silmaril.Courses.Cambridge.L2.Concrete.Precedence
public import Silmaril.Courses.Cambridge.Concrete.Lexer
public import Silmaril.Courses.Cambridge.L2.Syntax

/-! # A byte grammar for Cambridge L2

The constructors follow Sewell (2025–26), §4.6, pp. 65–67. In this profile
parentheses delimit compound expressions and arrow types. The outermost pair
may be omitted. Keyword forms delimit their operands inside their group.
A group contains a single expression, a binary/sequence production, or a
binary application. The parser produces named syntax before scope resolution. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.Concrete

open Silmaril.Courses.Cambridge.Concrete

abbrev expect := Silmaril.Courses.Cambridge.Concrete.expect

def readType : Nat → List Token → Option (Ty × List Token)
  | _ + 1, .keyword .int :: rest => some (.int, rest)
  | _ + 1, .keyword .bool :: rest => some (.bool, rest)
  | _ + 1, .keyword .unit :: rest => some (.unit, rest)
  | fuel + 1, .punct .openP :: rest => do
      let (domain, tail) ← readType fuel rest
      match tail with
      | .punct .closeP :: tail => return (domain, tail)
      | .punct .arrow :: tail =>
          let (codomain, tail) ← readType fuel tail
          let tail ← expect (.punct .closeP) tail
          return (.arr domain codomain, tail)
      | _ => none
  | _, _ => none

/-- Finish a group after reading its first operand. -/
def finishGroup (read : List Token → Option (RawExpr × List Token))
    (left : RawExpr) (tail : List Token) : Option (RawExpr × List Token) :=
  match tail with
  | .punct .closeP :: tail => return (left, tail)
  | .punct .add :: tail => do
      let (right, tail) ← read tail
      let tail ← expect (.punct .closeP) tail
      return (.binary left .add right, tail)
  | .punct .ge :: tail => do
      let (right, tail) ← read tail
      let tail ← expect (.punct .closeP) tail
      return (.binary left .ge right, tail)
  | .punct .seq :: tail => do
      let (right, tail) ← read tail
      let tail ← expect (.punct .closeP) tail
      return (.seq left right, tail)
  | tail => do
      let (right, tail) ← read tail
      let tail ← expect (.punct .closeP) tail
      return (.app left right, tail)

/-- One expression production, consuming a prefix of the token stream.
The remaining tokens are checked by the enclosing production or the entry point. -/
def readExpr : Nat → List Token → Option (RawExpr × List Token)
  | _ + 1, .number n :: rest => some (.int (Int.ofNat n), rest)
  | _ + 1, .punct .minus :: .number n :: rest => some (.int (-(Int.ofNat n)), rest)
  | _ + 1, .keyword .trueK :: rest => some (.bool true, rest)
  | _ + 1, .keyword .falseK :: rest => some (.bool false, rest)
  | _ + 1, .keyword .skip :: rest => some (.skip, rest)
  | _ + 1, .punct .deref :: .location name :: rest => some (.deref name, rest)
  | _ + 1, .variable name :: rest => some (.var name, rest)
  | fuel + 1, .punct .openP :: .location name :: .punct .assign :: rest => do
      let (value, tail) ← readExpr fuel rest
      let tail ← expect (.punct .closeP) tail
      return (.assign name value, tail)
  | fuel + 1, .punct .openP :: .keyword .ifK :: rest => do
      let (test, tail) ← readExpr fuel rest
      let tail ← expect (.keyword .thenK) tail
      let (yes, tail) ← readExpr fuel tail
      let tail ← expect (.keyword .elseK) tail
      let (no, tail) ← readExpr fuel tail
      let tail ← expect (.punct .closeP) tail
      return (.cond test yes no, tail)
  | fuel + 1, .punct .openP :: .keyword .whileK :: rest => do
      let (test, tail) ← readExpr fuel rest
      let tail ← expect (.keyword .doK) tail
      let (body, tail) ← readExpr fuel tail
      let tail ← expect (.keyword .doneK) tail
      let tail ← expect (.punct .closeP) tail
      return (.loop test body, tail)
  | fuel + 1, .punct .openP :: .keyword .funK :: .variable name :: .punct .colon :: rest => do
      let (domain, tail) ← readType fuel rest
      let tail ← expect (.punct .arrow) tail
      let (body, tail) ← readExpr fuel tail
      let tail ← expect (.punct .closeP) tail
      return (.lam name domain body, tail)
  | fuel + 1, .punct .openP :: .keyword .letK :: .variable name :: .punct .colon :: rest => do
      let (type, tail) ← readType fuel rest
      let tail ← expect (.punct .equals) tail
      let (value, tail) ← readExpr fuel tail
      let tail ← expect (.keyword .inK) tail
      let (body, tail) ← readExpr fuel tail
      let tail ← expect (.punct .closeP) tail
      return (.letE name type value body, tail)
  | fuel + 1, .punct .openP :: .keyword .letK :: .keyword .recK :: .variable function ::
      .punct .colon :: rest => do
      let (domain, tail) ← readType fuel rest
      let tail ← expect (.punct .arrow) tail
      let (codomain, tail) ← readType fuel tail
      let tail ← expect (.punct .equals) tail
      let .punct .openP :: .keyword .funK :: .variable parameter ::
        .punct .colon :: tail := tail | none
      let (parameterType, tail) ← readType fuel tail
      if parameterType ≠ domain then none else
        let tail ← expect (.punct .arrow) tail
        let (functionBody, tail) ← readExpr fuel tail
        let tail ← expect (.punct .closeP) tail
        let tail ← expect (.keyword .inK) tail
        let (body, tail) ← readExpr fuel tail
        let tail ← expect (.punct .closeP) tail
        return (.letRecFun function parameter domain codomain functionBody body, tail)
  | fuel + 1, .punct .openP :: rest => do
      let (left, tail) ← readExpr fuel rest
      finishGroup (readExpr fuel) left tail
  | _, _ => none

abbrev readWhole {α : Type} := @Silmaril.Courses.Cambridge.Concrete.readWhole α

def parse (bytes : ByteArray) : Option RawExpr :=
  tokenize bytes >>= readWithPrecedence readExpr Precedence.readExpr

def parseType (bytes : ByteArray) : Option Ty :=
  tokenize bytes >>= readWithPrecedence readType Precedence.readType

/-- Source binding is interpreted by the course's existing resolver.
Free variables are retained. There is no input spelling for de Bruijn indices. -/
def parseResolved (bytes : ByteArray) : Option Expr :=
  (parse bytes).map (RawExpr.resolve [])

def Parses (bytes : ByteArray) (term : RawExpr) : Prop := parse bytes = some term

def typeTokens : Ty → List Token
  | .int => [.keyword .int]
  | .bool => [.keyword .bool]
  | .unit => [.keyword .unit]
  | .arr domain codomain =>
      [.punct .openP] ++ typeTokens domain ++ [.punct .arrow] ++
        typeTokens codomain ++ [.punct .closeP]

def operator : Op → Token
  | .add => .punct .add
  | .ge => .punct .ge

def termTokens : RawExpr → List Token
  | .int (.ofNat n) => [.number n]
  | .int (.negSucc n) => [.punct .minus, .number (n + 1)]
  | .bool true => [.keyword .trueK]
  | .bool false => [.keyword .falseK]
  | .skip => [.keyword .skip]
  | .deref name => [.punct .deref, .location name]
  | .var name => [.variable name]
  | .assign name value => [.punct .openP, .location name, .punct .assign] ++ termTokens value ++ [.punct .closeP]
  | .binary left op right =>
      [.punct .openP] ++ termTokens left ++ [operator op] ++
        termTokens right ++ [.punct .closeP]
  | .seq left right =>
      [.punct .openP] ++ termTokens left ++ [.punct .seq] ++
        termTokens right ++ [.punct .closeP]
  | .cond test yes no =>
      [.punct .openP, .keyword .ifK] ++ termTokens test ++ [.keyword .thenK] ++
        termTokens yes ++ [.keyword .elseK] ++ termTokens no ++ [.punct .closeP]
  | .loop test body =>
      [.punct .openP, .keyword .whileK] ++ termTokens test ++ [.keyword .doK] ++
        termTokens body ++ [.keyword .doneK, .punct .closeP]
  | .lam name domain body =>
      [.punct .openP, .keyword .funK, .variable name, .punct .colon] ++ typeTokens domain ++
        [.punct .arrow] ++ termTokens body ++ [.punct .closeP]
  | .app function argument =>
      [.punct .openP] ++ termTokens function ++ termTokens argument ++ [.punct .closeP]
  | .letE name type value body =>
      [.punct .openP, .keyword .letK, .variable name, .punct .colon] ++ typeTokens type ++
        [.punct .equals] ++ termTokens value ++ [.keyword .inK] ++ termTokens body ++ [.punct .closeP]
  | .letRecFun function parameter domain codomain functionBody body =>
      [.punct .openP, .keyword .letK, .keyword .recK, .variable function, .punct .colon] ++ typeTokens domain ++
        [.punct .arrow] ++ typeTokens codomain ++
        [.punct .equals, .punct .openP, .keyword .funK, .variable parameter, .punct .colon] ++
        typeTokens domain ++ [.punct .arrow] ++ termTokens functionBody ++
        [.punct .closeP, .keyword .inK] ++ termTokens body ++ [.punct .closeP]

/-- The raw AST uses unrestricted strings. Only names in the source vocabulary
have an exact spelling. This condition is independent of typing and closedness. -/
def NamesOk : RawExpr → Prop
  | .int _ | .bool _ | .skip => True
  | .deref name => IsLocation name
  | .var name => IsVariable name
  | .assign name value => IsLocation name ∧ NamesOk value
  | .binary left _ right | .seq left right | .loop left right | .app left right =>
      NamesOk left ∧ NamesOk right
  | .cond test yes no => NamesOk test ∧ NamesOk yes ∧ NamesOk no
  | .lam name _ body => IsVariable name ∧ NamesOk body
  | .letE name _ value body => IsVariable name ∧ NamesOk value ∧ NamesOk body
  | .letRecFun function parameter _ _ functionBody body =>
      IsVariable function ∧ IsVariable parameter ∧ NamesOk functionBody ∧ NamesOk body

abbrev SourceExpr := {term : RawExpr // NamesOk term}

def print (term : SourceExpr) : ByteArray := render (termTokens term.val)
def printType (type : Ty) : ByteArray := render (typeTokens type)

end Silmaril.Courses.Cambridge.L2.Concrete
