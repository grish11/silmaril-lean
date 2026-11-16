module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite

@[expose] public section

/-!
# A concrete object indexed family: vectors of units

`Vector n` represents a unit-valued vector by its length together with the
index equation. The naturals are an existing object primitive; this specialized
Σ/Id construction does not implement arbitrary indexed W families. Its checked
derivations use one available universe and equality reflection.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.UnitVector

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

def numeral {k : ℕ} : ℕ → Tm k
  | 0 => .zero
  | n + 1 => .succ (numeral n)

/-- The equality family under a length binder. -/
def equation {k : ℕ} (n : ℕ) : Tm (k + 1) := .id .nats (.bv 0) (numeral n)

def Vector {k : ℕ} (n : ℕ) : Tm k := .sigma .nats (equation n)

def canonical {k : ℕ} (n : ℕ) : Tm k := .pair (numeral n) (.refl (numeral n))

def nil {k : ℕ} : Tm k := canonical 0

def cons {k : ℕ} (v : Tm k) : Tm k :=
  .pair (.succ (.fst v)) (.refl (.succ (.fst v)))

/-- Elimination from a fixed fibre uses its proved equality to the canonical vector. -/
def eliminate {k : ℕ} (c _v : Tm k) : Tm k := c

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.UnitVector
