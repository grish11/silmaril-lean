module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.SetSemantics.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.UnitVector.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Functions

@[expose] public section

/-! # Finite tags in the existing object language

The natural number is paired with a proof that its cutoff is zero. The cutoff
returns zero precisely below the supplied finite count, and one otherwise.
Thus the natural-number representation does not introduce extra family tags.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- A primitive-recursive zero/one test for strict membership below a count. -/
def cutoff : ℕ → {k : ℕ} → Tm k → Tm k
  | 0, _, _ => .succ .zero
  | count + 1, _, t => .natrec .nats (.abs .nats (cutoff count (.bv 1))) .zero t

/-- The finite object tag type, encoded using only Nat, Sigma and identity. -/
def Tag {k : ℕ} (count : ℕ) : Tm k :=
  .sigma .nats (.id .nats (cutoff count (.bv 0)) .zero)

/-- A concrete object representative for one member of the finite tag set. -/
def canonical {k : ℕ} {count : ℕ} (i : Fin count) : Tm k :=
  .pair (UnitVector.numeral i.val) (.refl .zero)

/-- Its concrete semantic zero/one result. -/
def code : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | count + 1, n + 1 => code count n

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag
