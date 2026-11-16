module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Motive.Thms
import Silmaril.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

/-- A concrete two-binder motive whose type depends on the endpoint variable. -/
def endpointMotive : ETm 2 := .id .unit .star (.bv 1)

/-- The endpoint-dependent motive has actual formation in both binder contexts. -/
theorem endpointMotive_formation {Γ : ECtx} (hΓ : ECtx.JEqH ∅ Γ .unit .star .star) :
    ∀ x ∉ Γ.dv, ∀ y ∉ (Γ.cons x .unit).dv,
      ECtx.JEqH ∅ ((Γ.cons x .unit).cons y (.id .unit .star (.fv x))) (.univ 0)
        ((endpointMotive.open x).open y) ((endpointMotive.open x).open y) := by
  intro x hx y hy
  have hId : ECtx.JEqH ∅ (.cons Γ x .unit) (.univ 0)
      (.id .unit .star (.fv x)) (.id .unit .star (.fv x)) :=
    endpointId_formation (.unit (n := 0) hΓ) hΓ hx
  have hOpen : (endpointMotive.open x).open y = .id .unit .star (.fv x) := by
    simp only [endpointMotive, ETm.open, show (1 : Fin 2) = Fin.last 1 from rfl, Fin.lastCases_last]
  simpa only [hOpen] using hId.weaken_last hy hId

/-- The endpoint-dependent motive is packaged from actual formation in both binder contexts. -/
theorem checked_endpoint_motive_packaging :
    ECtx.JEqH ∅ .nil (motiveType .unit .star 0)
      (packageMotive .unit .star endpointMotive) (packageMotive .unit .star endpointMotive) :=
  packageMotive_typing (.unit (n := 0) .nil_ok) .nil_ok (endpointMotive_formation .nil_ok)

/-- Direct double instantiation keeps the actual endpoint in the result type. -/
theorem endpointMotive_lst (b p : ETm 0) :
    (endpointMotive.lst b).lst p = .id .unit .star b := by
  simp only [endpointMotive, ETm.lst, show (1 : Fin 2) = Fin.last 1 from rfl, Fin.lastCases_last]
  congr 1
  simpa only [ETm.castLE_refl] using ETm.lst_castLE b (Nat.le_refl 0) p

/-- Packaged evaluation agrees with a nonconstant motive at any actual endpoint/path. -/
theorem checked_endpoint_motive_value {Γ : ECtx} {b p : ETm 0}
    (hΓ : ECtx.JEqH ∅ Γ .unit .star .star) (hb : ECtx.JEqH ∅ Γ .unit b b)
    (hp : ECtx.JEqH ∅ Γ (.id .unit .star b) p p) :
    ECtx.JEqH ∅ Γ (.univ 0) (value (packageMotive .unit .star endpointMotive) b p)
      (.id .unit .star b) := by
  simpa only [endpointMotive_lst] using
    packageMotive_value (.unit (n := 0) hΓ) hΓ (endpointMotive_formation hΓ) hb hp

/-- The base reflexivity term is transported to the direct endpoint-dependent instance. -/
theorem checked_endpoint_direct_elimination {Γ : ECtx} {b p : ETm 0}
    (hΓ : ECtx.JEqH ∅ Γ .unit .star .star) (hb : ECtx.JEqH ∅ Γ .unit b b)
    (hp : ECtx.JEqH ∅ Γ (.id .unit .star b) p p) :
    ECtx.JEqH ∅ Γ (.id .unit .star b) (.refl .star) (.refl .star) := by
  have hBase : ECtx.JEqH ∅ Γ ((endpointMotive.lst .star).lst (.refl .star))
      (.refl .star) (.refl .star) := by
    simpa only [endpointMotive_lst] using ECtx.JEqH.refl hΓ
  simpa only [endpointMotive_lst, basedJ] using
    directBasedJ_congr (.unit (n := 0) hΓ) hΓ (endpointMotive_formation hΓ) hb hp hBase

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination
