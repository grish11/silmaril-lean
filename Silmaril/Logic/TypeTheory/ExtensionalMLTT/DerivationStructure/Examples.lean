module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Weakening preserves the actual two-abstraction motive derivation through both cofinite binders. -/
theorem checked_unit_motive_weakening :
    ECtx.JEqH ∅ (.cons .nil "x" .nats)
      (IdentityElimination.motiveType .unit .star 0)
      IdentityElimination.unitMotive IdentityElimination.unitMotive :=
  (IdentityElimination.unitMotive_typing (H := ∅) .nil_ok).weaken_last
    (by simp [ECtx.dv]) (.nats (n := 0) .nil_ok)

/-- The old free variable keeps its exact lookup type after a fresh declaration is added. -/
theorem checked_old_variable_weakening :
    ECtx.JEqH ∅ ((ECtx.nil.cons "a" .nats).cons "b" .unit) .nats (.fv "a") (.fv "a") := by
  have hΓ : ECtx.JEqH ∅ (.cons .nil "a" .nats) .unit .star .star :=
    .cons_ok .nil_ok (by simp [ECtx.dv]) (.nats (n := 0) .nil_ok)
  have hv : ECtx.JEqH ∅ (.cons .nil "a" .nats) .nats (.fv "a") (.fv "a") :=
    .var hΓ (.here _ _ _)
  exact hv.weaken_last (by simp [ECtx.dv]) (.unit (n := 0) hΓ)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
