module

public import Silmaril.Logic.Algebraic.OrderSorted.Quotient.Defs

@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Presented
variable (T : Initial.Theory) {k : Nat} (Γ : Fin k → T.sig.base.S)

/-- Reflection is exactly the extra closure needed for quotient coercions to
remain injective in the original coherent model category. -/
theorem coherent : Coherent (algebra T Γ) where
  identity s x := by
    induction x using Quotient.inductionOn with
    | h a => rw [coerce_mk, Free.coerce_identity]
  injective h x y he := by
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        have hclasses : Quotient.mk (setoid T Γ _) (Free.coerce h a) =
            Quotient.mk _ (Free.coerce h b) :=
          (coerce_mk T Γ h a).symm.trans (he.trans (coerce_mk T Γ h b))
        exact Quotient.sound (Rel.reflect h (Quotient.exact hclasses))
  composition h j x := by
    induction x using Quotient.inductionOn with
    | h a => rw [coerce_mk, coerce_mk, coerce_mk, Free.coerce_composition]

end Silmaril.Logic.Algebraic.OrderSorted.Presented
