module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.SetSemantics.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding

universe u

noncomputable section

/-- The extended evaluator agrees with the original evaluator on every base term. -/
@[simp]
theorem term_denote (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (t : ETm k) :
    (term t).denote T ρ β = t.denote T ρ β := by
  induction t <;> simp_all [term, Tm.denote, ETm.denote]

/-- Agreement also holds for arbitrary, possibly finite, universe lookups. -/
@[simp]
theorem term_denoteIn (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (t : ETm k) :
    (term t).denoteIn U ρ β = t.denoteIn U ρ β := by
  induction t <;> simp_all [term, Tm.denoteIn, ETm.denoteIn]

/-- Context satisfaction is preserved and reflected by the syntax inclusion. -/
@[simp]
theorem context_sat (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) (Γ : ECtx) :
    (context Γ).Sat T ρ ↔ Γ.Sat T ρ := by
  induction Γ <;> simp_all [context, Ctx.Sat, ECtx.Sat]

/-- The base sentence map satisfies the semantic satisfaction condition. -/
@[simp]
theorem judgment_valid (T : SetHierarchy.{u}) (j : EJdg) :
    (judgment j).Valid T ↔ j.Valid T := by
  simp only [Jdg.Valid, EJdg.Valid, judgment, term_denote, context_sat]

/-- The same satisfaction condition holds for finite universe lookups. -/
@[simp]
theorem context_satIn (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) (Γ : ECtx) :
    (context Γ).SatIn U ρ ↔ Γ.SatIn U ρ := by
  induction Γ <;> simp_all [context, Ctx.SatIn, ECtx.SatIn]

@[simp]
theorem judgment_validIn (U : ℕ → ZFSet.{u}) (j : EJdg) :
    (judgment j).ValidIn U ↔ j.ValidIn U := by
  simp only [Jdg.ValidIn, EJdg.ValidIn, judgment, term_denoteIn, context_satIn]

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding
