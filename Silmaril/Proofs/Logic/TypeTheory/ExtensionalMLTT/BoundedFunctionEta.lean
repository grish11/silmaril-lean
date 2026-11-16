module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Structure.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.Thms

public section
namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedFunctionEta
open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.FunctionEta

private theorem family_weaken {Γ : ECtx} {levels n : ℕ} {A : ETm 0} {B : ETm 1} {L : Finset String}
    (hn : n < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    {x : String} (hxΓ : x ∉ Γ.dv) : ∀ y ∉ insert x (L ∪ Γ.dv),
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y A) (.univ n) (B.open y) (B.open y) := by
  have hcx := ECtx.JEqB.cons_ok hn hA.context hxΓ hA
  have hAx := hA.weaken_last hn hxΓ hA
  intro y hy
  have hyΓ : y ∉ Γ.dv := fun h => hy (Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right _ h)))
  have hyL : y ∉ L := fun h => hy (Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ h)))
  have hyx : y ≠ x := fun h => hy (Finset.mem_insert.mpr (Or.inl h))
  have hycx : y ∉ (Γ.cons x A).dv := by
    simpa only [ECtx.dv, Finset.mem_insert, not_or] using And.intro hyx hyΓ
  exact (hB y hyL).weaken (.cons_ok hn hcx hycx hAx)
    (ECtx.Embeds.cons (ECtx.Embeds.fresh hxΓ A) y A)

private theorem application_body {Γ : ECtx} {levels n : ℕ} {A f : ETm 0} {B : ETm 1} {L : Finset String}
    (hn : n < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : ECtx.JEqB levels ∅ Γ (.pi A B) f f) :
    ∀ x ∉ L ∪ Γ.dv, ECtx.JEqB levels ∅ (Γ.cons x A) (B.open x)
      ((ETm.app f.wk0 (.bv 0)).open x) ((ETm.app f.wk0 (.bv 0)).open x) := by
  intro x hx
  have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
  have hcx := ECtx.JEqB.cons_ok hn hf.context hxΓ hA
  have hAx := hA.weaken_last hn hxΓ hA
  have hfx := hf.weaken_last hn hxΓ hA
  have hBx := family_weaken hn hA hB hxΓ
  have happ := ECtx.JEqB.app hn hAx hBx hfx (ECtx.JEqB.var hcx (ECtx.Lookup.here ..))
  rw [body_open]
  simpa only [lst_fv] using happ

/-- The eta expansion of an actually typed dependent function has its original product type. -/
theorem expansion {Γ : ECtx} {levels n : ℕ} {A f : ETm 0} {B : ETm 1} {L : Finset String}
    (hn : n < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : ECtx.JEqB levels ∅ Γ (.pi A B) f f) :
    ECtx.JEqB levels ∅ Γ (.pi A B) (.abs A (.app f.wk0 (.bv 0))) (.abs A (.app f.wk0 (.bv 0))) := by
  apply ECtx.JEqB.abs (L := L ∪ Γ.dv) hn hA
  · intro x hx
    exact hB x (fun h => hx (Finset.mem_union_left _ h))
  · exact application_body hn hA hB hf

/-- Typed eta is derivable from function extensionality and beta in the target calculus. -/
theorem equality {Γ : ECtx} {levels n : ℕ} {A f : ETm 0} {B : ETm 1} {L : Finset String}
    (hn : n < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : ECtx.JEqB levels ∅ Γ (.pi A B) f f) :
    ECtx.JEqB levels ∅ Γ (.pi A B) (.abs A (.app f.wk0 (.bv 0))) f := by
  apply ECtx.JEqB.pi_ext (L := L ∪ Γ.dv) hn hA
    (fun x hx => hB x (fun h => hx (Finset.mem_union_left _ h))) (expansion hn hA hB hf) hf
  intro x hx
  have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
  have hcx := ECtx.JEqB.cons_ok hn hf.context hxΓ hA
  have hAx := hA.weaken_last hn hxΓ hA
  have hfx := hf.weaken_last hn hxΓ hA
  have hBx := family_weaken hn hA hB hxΓ
  have hv : ECtx.JEqB levels ∅ (Γ.cons x A) A (.fv x) (.fv x) := .var hcx (.here ..)
  have hb := ECtx.JEqB.beta_app hn hAx
    (fun y hy => hBx y (fun h => hy (Finset.mem_union_left _ h)))
    (application_body hn hAx hBx hfx) hv
  simpa only [lst_fv, body_open] using hb


end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedFunctionEta
