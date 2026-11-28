module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Basic

/-! # Scalars for the three-cycle equation -/

@[expose] public section

namespace Silmaril.Calco2019.CounterSemiring.ThreeCycle

/-- The finite values are bit sets of the three elements of the cyclic
group. The extra value `none` is the absorbing nonzero value. -/
structure Scalar where
  bits : Option (Fin 8)
  deriving DecidableEq

namespace Scalar

instance : Fintype Scalar :=
  Fintype.ofEquiv (Option (Fin 8)) ⟨Scalar.mk, bits, fun _ => rfl, fun ⟨_⟩ => rfl⟩

instance : Zero Scalar := ⟨⟨some 0⟩⟩
instance : One Scalar := ⟨⟨some 1⟩⟩

/-- The singleton of the order-three generator. -/
def generator : Scalar := ⟨some 2⟩

def mask (n : Nat) : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by decide)⟩

/-- Shift the finite set by the generator, cycling bit two into bit zero. -/
def rotate (n : Nat) : Nat := (n * 2) % 8 + n / 4

/-- Setwise product of two finite sets in the cyclic group. -/
def productBits (a b : Fin 8) : Fin 8 :=
  mask ((if a.val.testBit 0 then b.val else 0) |||
    (if a.val.testBit 1 then rotate b.val else 0) |||
    (if a.val.testBit 2 then rotate (rotate b.val) else 0))

instance : Add Scalar where
  add a b := match a.bits, b.bits with
    | some x, some y => ⟨some (mask (x.val ||| y.val))⟩
    | _, _ => ⟨none⟩

instance : Mul Scalar where
  mul a b :=
    if a = 0 ∨ b = 0 then 0
    else match a.bits, b.bits with
      | some x, some y => ⟨some (productBits x y)⟩
      | _, _ => ⟨none⟩

/-- Star sends the empty set and the identity singleton to the identity.
Every other scalar closes to the absorbing nonzero value. -/
def star (a : Scalar) : Scalar :=
  if a = 0 ∨ a = 1 then 1 else ⟨none⟩

/-- Scalar iteration with recurrence weight `a` and exit weight `b`. -/
def iterate (a b : Scalar) : Scalar := star a * b

end Scalar
end Silmaril.Calco2019.CounterSemiring.ThreeCycle
