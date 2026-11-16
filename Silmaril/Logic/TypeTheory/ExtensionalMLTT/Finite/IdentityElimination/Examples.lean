module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.IdentityElimination.Thms

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Bounded

/-- This two-binder motive depends on both the endpoint and the path variable. -/
def pathMotive : ETm 2 := .id (.id .unit .star (.bv 1)) (.bv 0) (.bv 0)

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

/-- Every member of the endpoint/path formation family shares the two-level budget. -/
theorem pathMotive_formation {Γ : ECtx} (hΓ : ECtx.JEqB 2 ∅ Γ .unit .star .star) :
    ∀ x ∉ Γ.dv, ∀ y ∉ (Γ.cons x .unit).dv,
      ECtx.JEqB 2 ∅ ((Γ.cons x .unit).cons y (.id .unit .star (.fv x))) (.univ 0)
        ((pathMotive.open x).open y) ((pathMotive.open x).open y) := by
  intro x hx y hy
  have hId : ECtx.JEqB 2 ∅ (Γ.cons x .unit) (.univ 0)
      (.id .unit .star (.fv x)) (.id .unit .star (.fv x)) :=
    endpointId_formation (by decide) (.unit (by decide) hΓ) hΓ hx
  have hctx : ECtx.JEqB 2 ∅ ((Γ.cons x .unit).cons y (.id .unit .star (.fv x))) .unit .star .star :=
    .cons_ok (by decide) hId.context hy hId
  have hOpen : (pathMotive.open x).open y = .id (.id .unit .star (.fv x)) (.fv y) (.fv y) := by
    simp only [pathMotive, ETm.open, show (1 : Fin 2) = Fin.last 1 from rfl, Fin.lastCases_last,
      show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl, Fin.lastCases_castSucc, lastCases_zero]
  simpa only [hOpen] using
    ECtx.JEqB.id (by decide) (hId.weaken hctx (ECtx.Embeds.fresh hy _))
      (.var hctx (.here _ _ _)) (.var hctx (.here _ _ _))

/-- Direct instantiation retains both the actual endpoint and the actual path. -/
theorem pathMotive_lst (b p : ETm 0) :
    (pathMotive.lst b).lst p = .id (.id .unit .star b) p p := by
  simp only [pathMotive, ETm.lst, show (1 : Fin 2) = Fin.last 1 from rfl, Fin.lastCases_last,
    show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl, Fin.lastCases_castSucc, lastCases_zero,
    ETm.castLE_refl]
  congr 2
  simpa only [ETm.castLE_refl] using ETm.lst_castLE b (Nat.le_refl 0) p

/-- The nonconstant endpoint/path motive packages with actual bounded abstractions. -/
theorem checked_path_motive_packaging :
    ECtx.JEqB 2 ∅ .nil (motiveType .unit .star 0)
      (packageMotive .unit .star pathMotive) (packageMotive .unit .star pathMotive) :=
  packageMotive_typing (k := 0) (by decide) (.unit (by decide) .nil_ok) .nil_ok (pathMotive_formation .nil_ok)

/-- Bounded reflection and UIP transport the base to the direct path-dependent result. -/
theorem checked_path_direct_elimination {Γ : ECtx} {b p : ETm 0}
    (hΓ : ECtx.JEqB 2 ∅ Γ .unit .star .star) (hb : ECtx.JEqB 2 ∅ Γ .unit b b)
    (hp : ECtx.JEqB 2 ∅ Γ (.id .unit .star b) p p) :
    ECtx.JEqB 2 ∅ Γ (.id (.id .unit .star b) p p) (.refl (.refl .star)) (.refl (.refl .star)) := by
  have hBase : ECtx.JEqB 2 ∅ Γ ((pathMotive.lst .star).lst (.refl .star))
      (.refl (.refl .star)) (.refl (.refl .star)) := by
    simpa only [pathMotive_lst] using ECtx.JEqB.refl (ECtx.JEqB.refl hΓ)
  simpa only [pathMotive_lst, basedJ] using
    directBasedJ_congr (k := 0) (by decide) (.unit (by decide) hΓ) hΓ (pathMotive_formation hΓ) hb hp hBase

/-- The endpoint/path-dependent example has a closed inhabited instance. -/
theorem checked_closed_path_direct_elimination :
    ECtx.JEqB 2 ∅ .nil (.id (.id .unit .star .star) (.refl .star) (.refl .star))
      (.refl (.refl .star)) (.refl (.refl .star)) :=
  checked_path_direct_elimination .nil_ok .nil_ok (.refl .nil_ok)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Bounded
