module

public import Silmaril.Courses.Cambridge.Concrete.Precedence
public import Silmaril.Courses.Cambridge.L2.Syntax

/-! Ordinary L2 precedence, also used by the L1 fragment check. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.Concrete.Precedence

open Silmaril.Courses.Cambridge.Concrete

def typeAtom (read : Reader Ty) : Reader Ty
  | .keyword .int :: rest => some (.int, rest)
  | .keyword .bool :: rest => some (.bool, rest)
  | .keyword .unit :: rest => some (.unit, rest)
  | .punct .openP :: rest => do
    let (type, tail) ← read rest
    return (type, ← expect (.punct .closeP) tail)
  | _ => none

def readType : Nat → Reader Ty
  | 0, _ => none
  | fuel + 1, tokens => chainRight (typeAtom (readType fuel)) .arrow .arr (fuel + 1) tokens

def readAtom (fuel : Nat) (read : Reader RawExpr) : Reader RawExpr
  | .number n :: rest => some (.int (Int.ofNat n), rest)
  | .punct .minus :: .number n :: rest => some (.int (-(Int.ofNat n)), rest)
  | .keyword .trueK :: rest => some (.bool true, rest)
  | .keyword .falseK :: rest => some (.bool false, rest)
  | .keyword .skip :: rest => some (.skip, rest)
  | .punct .deref :: .location name :: rest => some (.deref name, rest)
  | .variable name :: rest => some (.var name, rest)
  | .punct .openP :: rest => do
    let (expr, tail) ← read rest
    return (expr, ← expect (.punct .closeP) tail)
  | .keyword .ifK :: rest => do
    let (test, tail) ← read rest
    let (yes, tail) ← read (← expect (.keyword .thenK) tail)
    let (no, tail) ← read (← expect (.keyword .elseK) tail)
    return (.cond test yes no, tail)
  | .keyword .whileK :: rest => do
    let (test, tail) ← read rest
    let (body, tail) ← read (← expect (.keyword .doK) tail)
    return (.loop test body, ← expect (.keyword .doneK) tail)
  | .keyword .funK :: .variable name :: .punct .colon :: rest => do
    let (domain, tail) ← readBinderType (typeAtom (readType fuel)) .arr fuel rest
    let (body, tail) ← read tail
    return (.lam name domain body, tail)
  | .keyword .letK :: .variable name :: .punct .colon :: rest => do
    let (type, tail) ← readType fuel rest
    let (value, tail) ← read (← expect (.punct .equals) tail)
    let (body, tail) ← read (← expect (.keyword .inK) tail)
    return (.letE name type value body, tail)
  | .keyword .letK :: .keyword .recK :: .variable function :: .punct .colon :: rest => do
    let (.arr domain codomain, tail) ← readType fuel rest | none
    let .punct .openP :: .keyword .funK :: .variable parameter :: .punct .colon :: tail ←
      expect (.punct .equals) tail | none
    let (parameterType, tail) ← readBinderType (typeAtom (readType fuel)) .arr fuel tail
    if parameterType ≠ domain then none else
      let (functionBody, tail) ← read tail
      let tail ← expect (.punct .closeP) tail
      let (body, tail) ← read (← expect (.keyword .inK) tail)
      return (.letRecFun function parameter domain codomain functionBody body, tail)
  | _ => none

def readAssignment (operand : Reader RawExpr) : Reader RawExpr
  | .location name :: .punct .assign :: rest => do
    let (value, tail) ← operand rest
    return (.assign name value, tail)
  | tokens => operand tokens

def readExpr : Nat → Reader RawExpr
  | 0, _ => none
  | fuel + 1, tokens =>
    let app := readApplication (readAtom (fuel + 1) (readExpr fuel))
      startsArgument RawExpr.app (fuel + 1)
    let add := infixOnce app .add (fun left right => .binary left .add right)
    let comparison := infixOnce add .ge (fun left right => .binary left .ge right)
    chainRight (readAssignment comparison) .seq .seq (fuel + 1) tokens

end Silmaril.Courses.Cambridge.L2.Concrete.Precedence
