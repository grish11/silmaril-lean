module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Support.Defs

/-! # Infer a shared list of caller fields from the actual flat rows -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry

open LambdaSSA (FiniteCFG Flat)
open Morphism.CaseSSA (erase)

universe u
variable {F : Type u} {blocks exits labels n : Nat}

/-- Free value-variable occurrences at a flat body's boundary. Expression
occurrences use the existing erased LambdaSSA predicate. -/
def UsesVar : {m : Nat} → Flat F labels m → Nat → Prop
  | _, .br _ a, i => (erase a).UsesVar i
  | _, .let₁ a tail, i => (erase a).UsesVar i ∨ UsesVar tail (i + 1)
  | _, .let₂ a tail, i => (erase a).UsesVar i ∨ UsesVar tail (i + 2)
  | _, .case a l r, i => (erase a).UsesVar i ∨ UsesVar l (i + 1) ∨ UsesVar r (i + 1)

instance usesVarDecidable : {m : Nat} → (t : Flat F labels m) → (i : Nat) → Decidable (UsesVar t i)
  | _, .br _ a, i => inferInstanceAs (Decidable ((erase a).UsesVar i))
  | _, .let₁ a b, i =>
    letI := usesVarDecidable b (i + 1)
    inferInstanceAs (Decidable ((erase a).UsesVar i ∨ _))
  | _, .let₂ a b, i =>
    letI := usesVarDecidable b (i + 2)
    inferInstanceAs (Decidable ((erase a).UsesVar i ∨ _))
  | _, .case a l r, i =>
    letI := usesVarDecidable l (i + 1)
    letI := usesVarDecidable r (i + 1)
    inferInstanceAs (Decidable ((erase a).UsesVar i ∨ _ ∨ _))

/-- Take the union of older variable reads across all written rows. The
block argument occupies zero. Retain the caller's oldest-to-newest order. -/
def inferSlots (g : FiniteCFG F blocks exits n) : List (Fin n) :=
  (List.finRange n).reverse.filter fun slot =>
    (List.finRange blocks).any fun row => decide (UsesVar (g.block row) slot.succ.val)

end Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry
