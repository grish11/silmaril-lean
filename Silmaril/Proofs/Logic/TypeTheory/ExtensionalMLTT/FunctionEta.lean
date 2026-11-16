module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.DerivationSubstitution
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FunctionEta

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem closed_open (t : ETm 0) (x : String) : t.wk0.open x = t := by
  exact IdentityMotive.open_wkn_outermost t x

theorem body_open (f : ETm 0) (x : String) :
    (ETm.app f.wk0 (.bv 0)).open x = .app f (.fv x) := by
  simp only [ETm.open, ETm.wk0]
  change ETm.app (f.wk0.open x) (.fv x) = _
  rw [closed_open]

theorem lst_fv {k : ℕ} (t : ETm (k + 1)) (x : String) :
    t.lst (.fv x) = t.open x := by
  fun_induction ETm.lst t (.fv x) <;> simp_all [ETm.open, ETm.castLE]

private theorem family_weaken {Γ : ECtx} {n : ℕ} {A : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqH ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    {x : String} (hxΓ : x ∉ Γ.dv) : ∀ y ∉ insert x (L ∪ Γ.dv),
      ECtx.JEqH ∅ ((Γ.cons x A).cons y A) (.univ n) (B.open y) (B.open y) := by
  have hcx := ECtx.JEqH.cons_ok hA.context hxΓ hA
  have hAx := hA.weaken_last hxΓ hA
  intro y hy
  have hyΓ : y ∉ Γ.dv := fun h => hy (Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right _ h)))
  have hyL : y ∉ L := fun h => hy (Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ h)))
  have hyx : y ≠ x := fun h => hy (Finset.mem_insert.mpr (Or.inl h))
  have hycx : y ∉ (Γ.cons x A).dv := by
    simpa only [ECtx.dv, Finset.mem_insert, not_or] using And.intro hyx hyΓ
  exact (hB y hyL).weaken (.cons_ok hcx hycx hAx)
    (ECtx.Embeds.cons (ECtx.Embeds.fresh hxΓ A) y A)

private theorem application_body {Γ : ECtx} {n : ℕ} {A f : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqH ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : ECtx.JEqH ∅ Γ (.pi A B) f f) :
    ∀ x ∉ L ∪ Γ.dv, ECtx.JEqH ∅ (Γ.cons x A) (B.open x)
      ((ETm.app f.wk0 (.bv 0)).open x) ((ETm.app f.wk0 (.bv 0)).open x) := by
  intro x hx
  have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
  have hcx := ECtx.JEqH.cons_ok hf.context hxΓ hA
  have hAx := hA.weaken_last hxΓ hA
  have hfx := hf.weaken_last hxΓ hA
  have hBx := family_weaken hA hB hxΓ
  have happ := ECtx.JEqH.app hAx hBx hfx (ECtx.JEqH.var hcx (ECtx.Lookup.here ..))
  rw [body_open]
  simpa only [lst_fv] using happ

/-- The eta expansion of an actually typed dependent function has its original product type. -/
theorem expansion {Γ : ECtx} {n : ℕ} {A f : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqH ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : ECtx.JEqH ∅ Γ (.pi A B) f f) :
    ECtx.JEqH ∅ Γ (.pi A B) (.abs A (.app f.wk0 (.bv 0))) (.abs A (.app f.wk0 (.bv 0))) := by
  apply ECtx.JEqH.abs (L := L ∪ Γ.dv) hA
  · intro x hx
    exact hB x (fun h => hx (Finset.mem_union_left _ h))
  · exact application_body hA hB hf

/-- Typed eta is derivable from function extensionality and beta in the target calculus. -/
theorem equality {Γ : ECtx} {n : ℕ} {A f : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqH ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : ECtx.JEqH ∅ Γ (.pi A B) f f) :
    ECtx.JEqH ∅ Γ (.pi A B) (.abs A (.app f.wk0 (.bv 0))) f := by
  apply ECtx.JEqH.pi_ext (L := L ∪ Γ.dv) hA
    (fun x hx => hB x (fun h => hx (Finset.mem_union_left _ h))) (expansion hA hB hf) hf
  intro x hx
  have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
  have hcx := ECtx.JEqH.cons_ok hf.context hxΓ hA
  have hAx := hA.weaken_last hxΓ hA
  have hfx := hf.weaken_last hxΓ hA
  have hBx := family_weaken hA hB hxΓ
  have hv : ECtx.JEqH ∅ (Γ.cons x A) A (.fv x) (.fv x) := .var hcx (.here ..)
  have hb := ECtx.JEqH.beta_app hAx
    (fun y hy => hBx y (fun h => hy (Finset.mem_union_left _ h)))
    (application_body hAx hBx hfx) hv
  simpa only [lst_fv, body_open] using hb

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FunctionEta
