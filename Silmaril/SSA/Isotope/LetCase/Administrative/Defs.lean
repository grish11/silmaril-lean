module

public import Silmaril.SSA.Isotope.LetCase.Thms

/-! # Administrative moves on exact LetCase terms

A value is a bound variable, unit, or a pair of values. Binding a value
and taking a pair of values apart are administrative: a lowering that
packs values into a tuple on a jump and unpacks the tuple at the target
writes them, and they ask no request.

One pass removes every such binding that is visible in a term. A let of a
value is replaced by its body with the value substituted. A pattern let
of a pair of values is replaced by its body with the two values
substituted. A substitution can expose a new pair under a pattern let, so
the pass is iterated.
-/

@[expose] public section

namespace Silmaril.Isotope.LetCase.LocallyNameless.Tm

universe v w

variable {ν : Type w} {Φ : Type v}

/-- A value: a bound variable, unit, or a pair of values. -/
def isValue : {n : Nat} → Tm ν Φ n → Bool
  | _, .bv _ => true
  | _, .unit => true
  | _, .pair a b => isValue a && isValue b
  | _, _ => false

/-- The two components of a pair of values. -/
def valuePair : {n : Nat} → Tm ν Φ n → Option (Tm ν Φ n × Tm ν Φ n)
  | _, .pair a b => if isValue a && isValue b then some (a, b) else none
  | _, _ => none

/-- One pass of administrative moves: every let of a value and every
pattern let of a pair of values is replaced by its body, with the values
substituted. -/
def administrative : {n : Nat} → Tm ν Φ n → Tm ν Φ n
  | _, .fv x => .fv x
  | _, .bv i => .bv i
  | _, .op f a => .op f (administrative a)
  | _, .let₁ a b =>
    if isValue a then (administrative b).instantiate a
    else .let₁ (administrative a) (administrative b)
  | _, .unit => .unit
  | _, .pair a b => .pair (administrative a) (administrative b)
  | _, .let₂ a c =>
    match valuePair a with
    | some (x, y) => ((administrative c).instantiate y.lift).instantiate x
    | none => .let₂ (administrative a) (administrative c)
  | _, .inl a => .inl (administrative a)
  | _, .inr a => .inr (administrative a)
  | _, .case e l r => .case (administrative e) (administrative l) (administrative r)
  | _, .abort a => .abort (administrative a)

end Silmaril.Isotope.LetCase.LocallyNameless.Tm
