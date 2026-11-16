module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Thms

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

/-- Empty-theory elimination applies to an actual declared path variable. -/
theorem checked_unit_path_variable :
    ECtx.JEqH ∅ (.cons .nil "p" (.id .unit .star .star))
      (value unitMotive .star (.fv "p"))
      (basedJ .star .star (.fv "p")) (basedJ .star .star (.fv "p")) := by
  have hΓ : ECtx.JEqH ∅ (.cons .nil "p" (.id .unit .star .star)) .unit .star .star :=
    .cons_ok .nil_ok (by simp [ECtx.dv]) (.id (.unit (n := 1) .nil_ok) .nil_ok .nil_ok)
  exact basedJ_congr hΓ (.unit hΓ) (unitFiber_formed hΓ) (unitMotive_typing hΓ)
    hΓ hΓ (.var hΓ (.here _ _ _)) (unitMotive_base hΓ)

/-- The closed concrete base computes at reflexivity without any hypothesis leaf. -/
theorem checked_unit_beta :
    ECtx.JEqH ∅ .nil (value unitMotive .star (.refl .star))
      (basedJ .star .star (.refl .star)) .star :=
  basedJ_beta (unitMotive_base .nil_ok)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination
