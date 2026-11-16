module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Algebra.Defs

@[expose] public section

/-!
# Positive finite universe codes in the concrete quotient algebra

A realizer set is explicit data. The positive CodeLayer only refers to itself
in premise positions; universe result indices use an externally supplied
lower relation. Code supplies those lower relations by well-founded Nat
recursion, permitting U_j only below the current code level.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

noncomputable def FunctionSpace (X : Set (Value 0)) (Y : Value 0 → Set (Value 0)) : Set (Value 0) :=
  {f | ∀ a ∈ X, app f a ∈ Y a}
noncomputable def PairSpace (X : Set (Value 0)) (Y : Value 0 → Set (Value 0)) : Set (Value 0) :=
  {q | ∃ a ∈ X, ∃ b ∈ Y a, q = pair a b}
noncomputable def IdentitySpace (a b : Value 0) : Set (Value 0) :=
  {p | a = b ∧ p = refl a}

inductive CodeLayer (cap : ℕ)
    (lower : ∀ j, j < cap → Value 0 → Set (Value 0) → Prop) : Value 0 → Set (Value 0) → Prop
  | nat : CodeLayer cap lower nat Naturals
  | empty : CodeLayer cap lower empty ∅
  | unit : CodeLayer cap lower unit Units
  | univ (j : ℕ) (hj : j < cap) :
      CodeLayer cap lower (univ j) {q | ∃ X, lower j hj q X}
  | pi {A : Value 0} {B : Value 1} {X : Set (Value 0)} {Y : Value 0 → Set (Value 0)}
      (hA : CodeLayer cap lower A X)
      (hB : ∀ a ∈ X, CodeLayer cap lower (instantiate B a) (Y a)) :
      CodeLayer cap lower (pi A B) (FunctionSpace X Y)
  | sigma {A : Value 0} {B : Value 1} {X : Set (Value 0)} {Y : Value 0 → Set (Value 0)}
      (hA : CodeLayer cap lower A X)
      (hB : ∀ a ∈ X, CodeLayer cap lower (instantiate B a) (Y a)) :
      CodeLayer cap lower (sigma A B) (PairSpace X Y)
  | id {A a b : Value 0} {X : Set (Value 0)} (hA : CodeLayer cap lower A X)
      (ha : a ∈ X) (hb : b ∈ X) :
      CodeLayer cap lower (id A a b) (IdentitySpace a b)

noncomputable def Code (i : ℕ) : Value 0 → Set (Value 0) → Prop :=
  CodeLayer i (fun j _ => Code j)
termination_by i

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability
