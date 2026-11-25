module

public import Silmaril.Courses.Cambridge.L3.Concrete.Precedence
public import Silmaril.Courses.Cambridge.L3.NamedSyntax
public import Silmaril.Courses.Cambridge.L3.Concrete.Fields

/-! The grouped UTF-8 source profile for Sewell §5.5, pp. 78–82. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Concrete

open Silmaril.Courses.Cambridge.Concrete
def operator : Op → Token
  | .add => .punct .add
  | .ge => .punct .ge

def typeTokens : Ty → List Token
  | .int => [.keyword .int]
  | .bool => [.keyword .bool]
  | .unit => [.keyword .unit]
  | .arr left right =>
      [.punct .openP] ++ typeTokens left ++ [.punct .arrow] ++ typeTokens right ++ [.punct .closeP]
  | .prod left right =>
      [.punct .openP] ++ typeTokens left ++ [.punct .product] ++ typeTokens right ++ [.punct .closeP]
  | .sum left right =>
      [.punct .openP] ++ typeTokens left ++ [.punct .add] ++ typeTokens right ++ [.punct .closeP]
  | .ref contents =>
      .punct .openP :: typeTokens contents ++ [.keyword (.data .ref), .punct .closeP]
  | .record labels fields =>
      .punct .openBrace :: fieldsTokens .colon (recordEntries labels (fun i => typeTokens (fields i)))

def finishType (read : List Token → Option (Ty × List Token)) (left : Ty) :
    List Token → Option (Ty × List Token)
  | .punct .closeP :: tail => some (left, tail)
  | .keyword (.data .ref) :: .punct .closeP :: tail => some (.ref left, tail)
  | .punct .arrow :: tail => do
      let (right, tail) ← read tail
      let tail ← expect (.punct .closeP) tail
      return (.arr left right, tail)
  | .punct .product :: tail => do
      let (right, tail) ← read tail
      let tail ← expect (.punct .closeP) tail
      return (.prod left right, tail)
  | .punct .add :: tail => do
      let (right, tail) ← read tail
      let tail ← expect (.punct .closeP) tail
      return (.sum left right, tail)
  | _ => none

def readType : Nat → List Token → Option (Ty × List Token)
  | _ + 1, .keyword .int :: rest => some (.int, rest)
  | _ + 1, .keyword .bool :: rest => some (.bool, rest)
  | _ + 1, .keyword .unit :: rest => some (.unit, rest)
  | fuel + 1, .punct .openBrace :: rest =>
      readRecord Ty.record (readType fuel) .colon fuel rest
  | fuel + 1, .punct .openP :: rest => do
      let (type, tail) ← readType fuel rest
      finishType (readType fuel) type tail
  | _, _ => none

def finishExpr (read : List Token → Option (RawExpr × List Token))
    (left : RawExpr) (tail : List Token) : Option (RawExpr × List Token) :=
  match tail with
  | .punct .closeP :: tail => some (left, tail)
  | .punct .dot :: .variable label :: .punct .closeP :: tail => some (.project left label, tail)
  | .punct .add :: tail => binary (fun right => .binary left .add right) tail
  | .punct .ge :: tail => binary (fun right => .binary left .ge right) tail
  | .punct .seq :: tail => binary (.seq left) tail
  | .punct .assign :: tail => binary (.assign left) tail
  | .punct .comma :: tail => binary (.pair left) tail
  | tail => binary (.app left) tail
where
  binary (make : RawExpr → RawExpr) (tail : List Token) : Option (RawExpr × List Token) := do
    let (right, tail) ← read tail
    let tail ← expect (.punct .closeP) tail
    return (make right, tail)

/-- The branch binder is delimited by parentheses in the notes. -/
def readBranch (readType : List Token → Option (Ty × List Token))
    (read : List Token → Option (RawExpr × List Token)) :
    List Token → Option (Var × Ty × RawExpr × List Token)
  | .punct .openP :: .variable name :: .punct .colon :: rest => do
      let (type, tail) ← readType rest
      let tail ← expect (.punct .closeP) tail
      let tail ← expect (.punct .arrow) tail
      let (body, tail) ← read tail
      return (name, type, body, tail)
  | _ => none

/-- Read a term prefix. Each recursive operand consumes fewer production levels
than its parent, and the complete-input reader bounds depth by token count. -/
def readExpr : Nat → List Token → Option (RawExpr × List Token)
  | _ + 1, .number n :: rest => some (.int (Int.ofNat n), rest)
  | _ + 1, .punct .minus :: .number n :: rest => some (.int (-(Int.ofNat n)), rest)
  | _ + 1, .keyword .trueK :: rest => some (.bool true, rest)
  | _ + 1, .keyword .falseK :: rest => some (.bool false, rest)
  | _ + 1, .keyword .skip :: rest => some (.skip, rest)
  | _ + 1, .variable name :: rest => some (.var name, rest)
  | _ + 1, .location name :: rest => (readAddress name).map (fun loc => (.loc loc, rest))
  | fuel + 1, .punct .deref :: rest =>
      (readExpr fuel rest).map (fun (value, tail) => (.deref value, tail))
  | fuel + 1, .keyword (.data .ref) :: rest =>
      (readExpr fuel rest).map (fun (value, tail) => (.ref value, tail))
  | fuel + 1, .keyword (.data .fst) :: rest =>
      (readExpr fuel rest).map (fun (value, tail) => (.fst value, tail))
  | fuel + 1, .keyword (.data .snd) :: rest =>
      (readExpr fuel rest).map (fun (value, tail) => (.snd value, tail))
  | fuel + 1, .punct .openBrace :: rest =>
      readRecord RawExpr.record (readExpr fuel) .equals fuel rest
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
      -- Compare the parsed types, ignoring input whitespace and grouping.
      if typeTokens parameterType ≠ typeTokens domain then none else
        let tail ← expect (.punct .arrow) tail
        let (functionBody, tail) ← readExpr fuel tail
        let tail ← expect (.punct .closeP) tail
        let tail ← expect (.keyword .inK) tail
        let (body, tail) ← readExpr fuel tail
        let tail ← expect (.punct .closeP) tail
        return (.letRecFun function parameter domain codomain functionBody body, tail)
  | fuel + 1, .punct .openP :: .keyword (.data .inl) :: rest => do
      let (value, tail) ← readExpr fuel rest
      let tail ← expect (.punct .colon) tail
      let (type, tail) ← readType fuel tail
      let tail ← expect (.punct .closeP) tail
      return (.inl value type, tail)
  | fuel + 1, .punct .openP :: .keyword (.data .inr) :: rest => do
      let (value, tail) ← readExpr fuel rest
      let tail ← expect (.punct .colon) tail
      let (type, tail) ← readType fuel tail
      let tail ← expect (.punct .closeP) tail
      return (.inr value type, tail)
  | fuel + 1, .punct .openP :: .keyword (.data .matchK) :: rest => do
      let (value, tail) ← readExpr fuel rest
      let tail ← expect (.keyword (.data .withK)) tail
      let tail ← expect (.keyword (.data .inl)) tail
      let (x, typeX, left, tail) ← readBranch (readType fuel) (readExpr fuel) tail
      let tail ← expect (.punct .bar) tail
      let tail ← expect (.keyword (.data .inr)) tail
      let (y, typeY, right, tail) ← readBranch (readType fuel) (readExpr fuel) tail
      let tail ← expect (.punct .closeP) tail
      return (.matchSum value x typeX left y typeY right, tail)
  | fuel + 1, .punct .openP :: rest => do
      let (left, tail) ← readExpr fuel rest
      finishExpr (readExpr fuel) left tail
  | _, _ => none

def parse (bytes : ByteArray) : Option RawExpr :=
  lex bytes >>= readWithPrecedence readExpr (Precedence.readExpr fun a b => typeTokens a == typeTokens b)

def parseType (bytes : ByteArray) : Option Ty :=
  lex bytes >>= readWithPrecedence readType Precedence.readType
def parseResolved (bytes : ByteArray) : Option Expr := (parse bytes).map (RawExpr.resolve [])

def Parses (bytes : ByteArray) (term : RawExpr) : Prop := parse bytes = some term

def branchTokens (name : Var) (type : Ty) (body : List Token) : List Token :=
  [.punct .openP, .variable name, .punct .colon] ++ typeTokens type ++
    [.punct .closeP, .punct .arrow] ++ body

def termTokens : RawExpr → List Token
  | .int (.ofNat n) => [.number n]
  | .int (.negSucc n) => [.punct .minus, .number (n + 1)]
  | .bool true => [.keyword .trueK]
  | .bool false => [.keyword .falseK]
  | .skip => [.keyword .skip]
  | .var name => [.variable name]
  | .loc address => [addressToken address]
  | .deref value => .punct .deref :: termTokens value
  | .ref value => .keyword (.data .ref) :: termTokens value
  | .fst value => .keyword (.data .fst) :: termTokens value
  | .snd value => .keyword (.data .snd) :: termTokens value
  | .binary left op right =>
      [.punct .openP] ++ termTokens left ++ [operator op] ++ termTokens right ++ [.punct .closeP]
  | .assign left right =>
      [.punct .openP] ++ termTokens left ++ [.punct .assign] ++ termTokens right ++ [.punct .closeP]
  | .seq left right =>
      [.punct .openP] ++ termTokens left ++ [.punct .seq] ++ termTokens right ++ [.punct .closeP]
  | .pair left right =>
      [.punct .openP] ++ termTokens left ++ [.punct .comma] ++ termTokens right ++ [.punct .closeP]
  | .app function argument =>
      [.punct .openP] ++ termTokens function ++ termTokens argument ++ [.punct .closeP]
  | .cond test yes no =>
      [.punct .openP, .keyword .ifK] ++ termTokens test ++ [.keyword .thenK] ++
        termTokens yes ++ [.keyword .elseK] ++ termTokens no ++ [.punct .closeP]
  | .loop test body =>
      [.punct .openP, .keyword .whileK] ++ termTokens test ++ [.keyword .doK] ++
        termTokens body ++ [.keyword .doneK, .punct .closeP]
  | .lam name domain body =>
      [.punct .openP, .keyword .funK, .variable name, .punct .colon] ++ typeTokens domain ++
        [.punct .arrow] ++ termTokens body ++ [.punct .closeP]
  | .letE name type value body =>
      [.punct .openP, .keyword .letK, .variable name, .punct .colon] ++ typeTokens type ++
        [.punct .equals] ++ termTokens value ++ [.keyword .inK] ++ termTokens body ++ [.punct .closeP]
  | .letRecFun function parameter domain codomain functionBody body =>
      [.punct .openP, .keyword .letK, .keyword .recK, .variable function, .punct .colon] ++
        typeTokens domain ++ [.punct .arrow] ++ typeTokens codomain ++
        [.punct .equals, .punct .openP, .keyword .funK, .variable parameter, .punct .colon] ++
        typeTokens domain ++ [.punct .arrow] ++ termTokens functionBody ++
        [.punct .closeP, .keyword .inK] ++ termTokens body ++ [.punct .closeP]
  | .inl value type =>
      [.punct .openP, .keyword (.data .inl)] ++ termTokens value ++
        [.punct .colon] ++ typeTokens type ++ [.punct .closeP]
  | .inr value type =>
      [.punct .openP, .keyword (.data .inr)] ++ termTokens value ++
        [.punct .colon] ++ typeTokens type ++ [.punct .closeP]
  | .matchSum value x typeX left y typeY right =>
      [.punct .openP, .keyword (.data .matchK)] ++ termTokens value ++
        [.keyword (.data .withK), .keyword (.data .inl)] ++ branchTokens x typeX (termTokens left) ++
        [.punct .bar, .keyword (.data .inr)] ++ branchTokens y typeY (termTokens right) ++
        [.punct .closeP]
  | .record labels fields =>
      .punct .openBrace :: fieldsTokens .equals (recordEntries labels (fun i => termTokens (fields i)))
  | .project value label =>
      [.punct .openP] ++ termTokens value ++ [.punct .dot, .variable label, .punct .closeP]

/-- The source domain restricts names without changing the course ASTs.
Record ordering and uniqueness already reside in `RecordLabels`. -/
def TypeNamesOk : Ty → Prop
  | .int | .bool | .unit => True
  | .arr left right | .prod left right | .sum left right => TypeNamesOk left ∧ TypeNamesOk right
  | .ref value => TypeNamesOk value
  | .record labels fields => ∀ i, IsName (labels.label i) ∧ TypeNamesOk (fields i)

def NamesOk : RawExpr → Prop
  | .int _ | .bool _ | .skip | .loc _ => True
  | .var name => IsName name
  | .assign left right | .binary left _ right | .seq left right | .loop left right
  | .app left right | .pair left right => NamesOk left ∧ NamesOk right
  | .deref value | .ref value | .fst value | .snd value => NamesOk value
  | .cond test yes no => NamesOk test ∧ NamesOk yes ∧ NamesOk no
  | .lam name type body => IsName name ∧ TypeNamesOk type ∧ NamesOk body
  | .letE name type value body => IsName name ∧ TypeNamesOk type ∧ NamesOk value ∧ NamesOk body
  | .letRecFun fn param domain codomain value body =>
      IsName fn ∧ IsName param ∧ TypeNamesOk domain ∧ TypeNamesOk codomain ∧ NamesOk value ∧ NamesOk body
  | .inl value type | .inr value type => NamesOk value ∧ TypeNamesOk type
  | .matchSum value x typeX left y typeY right =>
      NamesOk value ∧ IsName x ∧ TypeNamesOk typeX ∧ NamesOk left ∧
        IsName y ∧ TypeNamesOk typeY ∧ NamesOk right
  | .record labels fields => ∀ i, IsName (labels.label i) ∧ NamesOk (fields i)
  | .project value label => NamesOk value ∧ IsName label

abbrev SourceExpr := {term : RawExpr // NamesOk term}
abbrev SourceType := {type : Ty // TypeNamesOk type}

def print (term : SourceExpr) : ByteArray := renderL3 (termTokens term.val)
def printType (type : SourceType) : ByteArray := renderL3 (typeTokens type.val)

end Silmaril.Courses.Cambridge.L3.Concrete
