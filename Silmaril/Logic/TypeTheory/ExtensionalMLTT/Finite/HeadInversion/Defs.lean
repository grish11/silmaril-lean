module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Assignments.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Product and sum heads carry actual component formation within a common rule budget. -/
def ETm.HeadFormedB (levels : ℕ) (Γ : ECtx) : ETm 0 → Prop
  | .pi A B | .sigma A B => ∃ n : ℕ, n < levels ∧ ∃ L : Finset String,
      ECtx.JEqB levels ∅ Γ (.univ n) A A ∧ ∀ x ∉ L,
        ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x)
  | _ => True

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
