module

public import Silmaril.Courses.Cambridge.Concrete.Precedence
public import Silmaril.Courses.Cambridge.L3.NamedSyntax
public import Silmaril.Courses.Cambridge.L3.Concrete.Fields

/-! Ordinary L3 precedence for terms and types. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Concrete.Precedence

open Silmaril.Courses.Cambridge.Concrete

def typeAtom (read : Reader Ty) (fuel : Nat) : Reader Ty
  | .keyword .int :: rest => some (.int, rest)
  | .keyword .bool :: rest => some (.bool, rest)
  | .keyword .unit :: rest => some (.unit, rest)
  | .punct .openP :: rest => do
    let (type, tail) ← read rest
    return (type, ← expect (.punct .closeP) tail)
  | .punct .openBrace :: rest => readRecord Ty.record read .colon fuel rest
  | _ => none

def finishRef : Nat → Ty → Reader Ty
  | 0, _, _ => none
  | fuel + 1, type, .keyword (.data .ref) :: rest => finishRef fuel (.ref type) rest
  | _ + 1, type, rest => some (type, rest)

def readNonArrowType (read : Reader Ty) (fuel : Nat) : Reader Ty :=
  let readRef : Reader Ty := fun tokens => do
    let (type, tail) ← typeAtom read fuel tokens
    finishRef fuel type tail
  infixOnce (infixOnce readRef .product .prod) .add .sum

def readType : Nat → Reader Ty
  | 0, _ => none
  | fuel + 1, tokens => chainRight (readNonArrowType (readType fuel) (fuel + 1))
      .arrow .arr (fuel + 1) tokens

def readPairOrGroup (read : Reader RawExpr) : Reader RawExpr := fun tokens => do
  let (left, tail) ← read tokens
  match tail with
  | .punct .comma :: rest => do
    let (right, tail) ← read rest
    return (.pair left right, ← expect (.punct .closeP) tail)
  | _ => return (left, ← expect (.punct .closeP) tail)

def readBranch (readType : Reader Ty) (read : Reader RawExpr) :
    Reader (Var × Ty × RawExpr)
  | .punct .openP :: .variable name :: .punct .colon :: rest => do
    let (type, tail) ← readType rest
    let tail ← expect (.punct .closeP) tail
    let (body, tail) ← read (← expect (.punct .arrow) tail)
    return ((name, type, body), tail)
  | _ => none

def readInjection (make : RawExpr → Ty → RawExpr) (readType : Reader Ty)
    (read : Reader RawExpr) : Reader RawExpr := fun tokens => do
  let (value, tail) ← read tokens
  let (type, tail) ← readType (← expect (.punct .colon) tail)
  return (make value type, tail)

def readAtom (read : Reader RawExpr) (sameType : Ty → Ty → Bool) : Nat → Reader RawExpr
  | _ + 1, .number n :: rest => some (.int (Int.ofNat n), rest)
  | _ + 1, .punct .minus :: .number n :: rest => some (.int (-(Int.ofNat n)), rest)
  | _ + 1, .keyword .trueK :: rest => some (.bool true, rest)
  | _ + 1, .keyword .falseK :: rest => some (.bool false, rest)
  | _ + 1, .keyword .skip :: rest => some (.skip, rest)
  | _ + 1, .variable name :: rest => some (.var name, rest)
  | _ + 1, .location name :: rest => (readAddress name).map fun loc => (.loc loc, rest)
  | fuel + 1, .punct .deref :: rest =>
    (readAtom read sameType fuel rest).map fun (arg, tail) => (.deref arg, tail)
  | fuel + 1, .keyword (.data .ref) :: rest =>
    (readAtom read sameType fuel rest).map fun (arg, tail) => (.ref arg, tail)
  | fuel + 1, .keyword (.data .fst) :: rest =>
    (readAtom read sameType fuel rest).map fun (arg, tail) => (.fst arg, tail)
  | fuel + 1, .keyword (.data .snd) :: rest =>
    (readAtom read sameType fuel rest).map fun (arg, tail) => (.snd arg, tail)
  | _ + 1, .punct .openP :: rest => readPairOrGroup read rest
  | fuel + 1, .punct .openBrace :: rest =>
    readRecord RawExpr.record read .equals (fuel + 1) rest
  | _ + 1, .keyword .ifK :: rest => do
    let (test, tail) ← read rest
    let (yes, tail) ← read (← expect (.keyword .thenK) tail)
    let (no, tail) ← read (← expect (.keyword .elseK) tail)
    return (.cond test yes no, tail)
  | _ + 1, .keyword .whileK :: rest => do
    let (test, tail) ← read rest
    let (body, tail) ← read (← expect (.keyword .doK) tail)
    return (.loop test body, ← expect (.keyword .doneK) tail)
  | fuel + 1, .keyword .funK :: .variable name :: .punct .colon :: rest => do
    let (domain, tail) ← readBinderType (readNonArrowType (readType fuel) (fuel + 1))
      .arr (fuel + 1) rest
    let (body, tail) ← read tail
    return (.lam name domain body, tail)
  | fuel + 1, .keyword .letK :: .variable name :: .punct .colon :: rest => do
    let (type, tail) ← readType (fuel + 1) rest
    let (value, tail) ← read (← expect (.punct .equals) tail)
    let (body, tail) ← read (← expect (.keyword .inK) tail)
    return (.letE name type value body, tail)
  | fuel + 1, .keyword .letK :: .keyword .recK :: .variable function :: .punct .colon :: rest => do
    let (.arr domain codomain, tail) ← readType (fuel + 1) rest | none
    let .punct .openP :: .keyword .funK :: .variable parameter :: .punct .colon :: tail ←
      expect (.punct .equals) tail | none
    let (parameterType, tail) ← readBinderType (readNonArrowType (readType fuel) (fuel + 1))
      .arr (fuel + 1) tail
    if !sameType parameterType domain then none else
      let (functionBody, tail) ← read tail
      let tail ← expect (.punct .closeP) tail
      let (body, tail) ← read (← expect (.keyword .inK) tail)
      return (.letRecFun function parameter domain codomain functionBody body, tail)
  | fuel + 1, .keyword (.data .inl) :: rest => readInjection .inl (readType (fuel + 1)) read rest
  | fuel + 1, .keyword (.data .inr) :: rest => readInjection .inr (readType (fuel + 1)) read rest
  | fuel + 1, .keyword (.data .matchK) :: rest => do
    let (value, tail) ← read rest
    let tail ← expect (.keyword (.data .withK)) tail
    let tail ← expect (.keyword (.data .inl)) tail
    let ((x, typeX, left), tail) ← readBranch (readType (fuel + 1)) read tail
    let tail ← expect (.punct .bar) tail
    let tail ← expect (.keyword (.data .inr)) tail
    let ((y, typeY, right), tail) ← readBranch (readType (fuel + 1)) read tail
    return (.matchSum value x typeX left y typeY right, tail)
  | _, _ => none

def finishProjection : Nat → RawExpr → Reader RawExpr
  | 0, _, _ => none
  | fuel + 1, value, .punct .dot :: .variable label :: rest =>
    finishProjection fuel (.project value label) rest
  | _ + 1, value, rest => some (value, rest)

def startsArgument : List Token → Bool
  | .location _ :: _ | .punct .openBrace :: _
  | .keyword (.data .ref) :: _ | .keyword (.data .fst) :: _ | .keyword (.data .snd) :: _ => true
  | tokens => Cambridge.Concrete.startsArgument tokens

def readExpr (sameType : Ty → Ty → Bool) : Nat → Reader RawExpr
  | 0, _ => none
  | fuel + 1, tokens =>
    let operand : Reader RawExpr := fun tokens => do
      let (value, tail) ← readAtom (readExpr sameType fuel) sameType (fuel + 1) tokens
      finishProjection (fuel + 1) value tail
    let app := readApplication operand startsArgument RawExpr.app (fuel + 1)
    let add := infixOnce app .add (fun left right => .binary left .add right)
    let comparison := infixOnce add .ge (fun left right => .binary left .ge right)
    let assignment := infixOnce comparison .assign .assign
    chainRight assignment .seq .seq (fuel + 1) tokens

end Silmaril.Courses.Cambridge.L3.Concrete.Precedence
