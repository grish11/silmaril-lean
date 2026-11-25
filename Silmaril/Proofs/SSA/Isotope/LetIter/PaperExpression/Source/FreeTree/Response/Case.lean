module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

/-! # Observing both injections and reflecting their effectful case arms -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case.Proofs

universe u v w

section Source

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A B C X : τ} {e : ε} {l r l' r' : Expr Φ}

private theorem wk1_var (slot : τ × ε) (i : Fin (((X, (⊥ : ε)) :: Γ).length)) :
    Wf ((X, (⊥ : ε)) :: slot :: Γ) (Expr.var (Expr.liftWk Nat.succ i.val) : Expr Φ)
      ((((X, (⊥ : ε)) :: Γ).get i).1) ((((X, (⊥ : ε)) :: Γ).get i).2) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Wf.var (Γ := (X, ⊥) :: slot :: Γ) 0 le_rfl
  · exact Wf.var (Γ := (X, ⊥) :: slot :: Γ) j.succ.succ le_rfl

private theorem wf_wk1 (slot : τ × ε) (hl : Wf ((X, (⊥ : ε)) :: Γ) l C e) :
    Wf ((X, (⊥ : ε)) :: slot :: Γ) l.wk1 C e := by
  rw [Expr.wk1, Expr.wk_eq_subst]
  exact hl.subst_typed (wk1_var slot)

private theorem eqv_wk1 (slot : τ × ε) (hl : Eqv ((X, (⊥ : ε)) :: Γ) C e l r) :
    Eqv ((X, (⊥ : ε)) :: slot :: Γ) C e l.wk1 r.wk1 :=
  hl.wk_typed (ρ := Expr.liftWk Nat.succ) (wk1_var slot)

public theorem source_wf (hl : Wf ((A, (⊥ : ε)) :: Γ) l C e)
    (hr : Wf ((B, (⊥ : ε)) :: Γ) r C e) :
    Wf ((coprod A B, (⊥ : ε)) :: Γ) (onHead l r) C e :=
  .case (.var 0 bot_le) (wf_wk1 _ hl) (wf_wk1 _ hr)

private theorem specialization_wk1 (a p : Expr Φ) :
    a.wk1.subst (Expr.liftSubst (SumSplit.replaceVar 0 p)) = a.wk1 := by
  rw [Expr.wk1, Expr.subst_wk, Expr.wk_eq_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => rfl

private theorem beta_wk1 (a : Expr Φ) :
    a.wk1.subst (Expr.var 0 : Expr Φ).subst0 = a := by
  rw [Expr.wk1, Expr.subst_wk]
  have h : (Expr.var 0 : Expr Φ).subst0 ∘ Expr.liftWk Nat.succ = Expr.var := by
    funext i
    cases i <;> rfl
  rw [h, Expr.subst_var]

public theorem specialize_left (hl : Wf ((A, (⊥ : ε)) :: Γ) l C e)
    (hr : Wf ((B, (⊥ : ε)) :: Γ) r C e) :
    Eqv ((A, (⊥ : ε)) :: Γ) C e (SumSplit.left 0 (onHead l r)) l := by
  have htag : KnownTag ((A, (⊥ : ε)) :: Γ) A B e (.inl (.var 0) : Expr Φ) (.inl (.var 0)) :=
    .inl (.var 0 bot_le)
  have hl' := wf_wk1 (A, (⊥ : ε)) hl
  have hr' := wf_wk1 (A, (⊥ : ε)) hr
  have hcase := htag.case_eqv hl' hr'
  have hstep : Eqv ((A, (⊥ : ε)) :: Γ) C e (.let₁ (.var 0) l.wk1)
      (l.wk1.subst (Expr.var 0 : Expr Φ).subst0) :=
    .step (.let1_beta (Wf.var (Γ := (A, ⊥) :: Γ) 0 le_rfl) hl')
  have hbeta := beta_wk1 l ▸ hstep
  have hsplit : SumSplit.left 0 (onHead l r) = .case (.inl (.var 0)) l.wk1 r.wk1 := by
    simp only [SumSplit.left, onHead, Expr.subst, specialization_wk1]
    rfl
  exact hsplit.symm ▸ hcase.trans hbeta

public theorem specialize_right (hl : Wf ((A, (⊥ : ε)) :: Γ) l C e)
    (hr : Wf ((B, (⊥ : ε)) :: Γ) r C e) :
    Eqv ((B, (⊥ : ε)) :: Γ) C e (SumSplit.right 0 (onHead l r)) r := by
  have htag : KnownTag ((B, (⊥ : ε)) :: Γ) A B e (.inr (.var 0) : Expr Φ) (.inr (.var 0)) :=
    .inr (.var 0 bot_le)
  have hl' := wf_wk1 (B, (⊥ : ε)) hl
  have hr' := wf_wk1 (B, (⊥ : ε)) hr
  have hcase := htag.case_eqv hl' hr'
  have hstep : Eqv ((B, (⊥ : ε)) :: Γ) C e (.let₁ (.var 0) r.wk1)
      (r.wk1.subst (Expr.var 0 : Expr Φ).subst0) :=
    .step (.let1_beta (Wf.var (Γ := (B, ⊥) :: Γ) 0 le_rfl) hr')
  have hbeta := beta_wk1 r ▸ hstep
  have hsplit : SumSplit.right 0 (onHead l r) = .case (.inr (.var 0)) l.wk1 r.wk1 := by
    simp only [SumSplit.right, onHead, Expr.subst, specialization_wk1]
    rfl
  exact hsplit.symm ▸ hcase.trans hbeta

public theorem eqv_iff_arms (hl : Wf ((A, (⊥ : ε)) :: Γ) l C e)
    (hr : Wf ((B, (⊥ : ε)) :: Γ) r C e)
    (hl' : Wf ((A, (⊥ : ε)) :: Γ) l' C e) (hr' : Wf ((B, (⊥ : ε)) :: Γ) r' C e) :
    Eqv ((coprod A B, (⊥ : ε)) :: Γ) C e (onHead l r) (onHead l' r') ↔
      Eqv ((A, (⊥ : ε)) :: Γ) C e l l' ∧ Eqv ((B, (⊥ : ε)) :: Γ) C e r r' := by
  constructor
  · intro h
    have he := (SumSplit.eqv_iff_specializations (A := A) (B := B) 0 rfl rfl
      (source_wf hl hr) (source_wf hl' hr')).mp h
    exact ⟨(specialize_left hl hr).symm.trans (he.1.trans (specialize_left hl' hr')),
      (specialize_right hl hr).symm.trans (he.2.trans (specialize_right hl' hr'))⟩
  · rintro ⟨heL, heR⟩
    exact .case (.refl (.var 0 bot_le)) (eqv_wk1 _ heL) (eqv_wk1 _ heR)

end Source

section Reflection

variable {α Φ : Type u} (S : Signature α Φ) {ε : Type w}
  [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] [DecidableEq α]
  {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α} {x y c : α} {e : ε}

local notation "Γ₊" => ((Ty.coprod (Ty.base x) (Ty.base y), (⊥ : ε)) :: Γ)
local notation "ΓL" => ((Ty.base x, (⊥ : ε)) :: Γ)
local notation "ΓR" => ((Ty.base y, (⊥ : ε)) :: Γ)

omit [HasEff Φ ε] [EffectIteration ε] [DecidableEq α] in
private theorem extended_pure {A : Ty α} (hΓ : Γ.Pure) :
    EffectCtx.Pure ((A, (⊥ : ε)) :: Γ) :=
  fun i => Fin.cases (motive := fun j => (((A, (⊥ : ε)) :: Γ).get j).2 = ⊥) rfl hΓ i

omit [HasEff Φ ε] [EffectIteration ε] [DecidableEq α] in
private theorem extended_slots (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (a : α) :
    ∀ i : Fin (Γ.length + 1),
      (((Ty.base a, (⊥ : ε)) :: Γ).get i).1 = .base (extendSorts a ts i) :=
  fun i => Fin.cases (motive := fun j =>
    (((Ty.base a, (⊥ : ε)) :: Γ).get j).1 = .base (extendSorts a ts j)) rfl hslots i

private theorem reflect_arm {Δ : EffectCtx (Ty α) ε} {slots : Fin Δ.length → α}
    (hΔ : Δ.Pure) (hs : ∀ i, (Δ.get i).1 = .base (slots i))
    (p q : Flatten.Program S slots c) (hp : Flatten.Program.WellTyped S e p)
    (hq : Flatten.Program.WellTyped S e q) {a b : Expr Φ} {t s : Tm Empty Φ Δ.length}
    (ht : a.toLetIter Δ.length = some t) (ht' : b.toLetIter Δ.length = some s)
    (el : letI := S.endpoints; Eqv Δ (.base c) e a p.source)
    (er : letI := S.endpoints; Eqv Δ (.base c) e b q.source)
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Δ.toBoundCtx t s (.base c)) :
    letI := S.endpoints
    Eqv Δ (.base c) e p.source q.source := by
  let instr := S.endpoints
  obtain ⟨_, hp₀, _⟩ := (Flatten.source_wf S hΔ hs e p hp).toLetIter
  obtain ⟨_, hq₀, _⟩ := (Flatten.source_wf S hΔ hs e q hq).toLetIter
  have hl := el.toLetIter ht hp₀
  have hr := er.toLetIter ht' hq₀
  exact (Flatten.endpoint_reflection S hΔ hs e p q hp hq hp₀ hq₀).mp
    (hl.symm.trans (hn.trans hr))

public theorem arms_eqv_of_native (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (l l' : Flatten.Program S (extendSorts x ts) c) (r r' : Flatten.Program S (extendSorts y ts) c)
    (hl : Flatten.Program.WellTyped S e l) (hl' : Flatten.Program.WellTyped S e l')
    (hr : Flatten.Program.WellTyped S e r) (hr' : Flatten.Program.WellTyped S e r')
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : (onHead l.source r.source).toLetIter (Γ.length + 1) = some t)
    (ht' : (onHead l'.source r'.source).toLetIter (Γ.length + 1) = some s)
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) (EffectCtx.toBoundCtx Γ₊) t s (.base c)) :
    letI := S.endpoints
    Eqv ΓL (.base c) e l.source l'.source ∧ Eqv ΓR (.base c) e r.source r'.source := by
  let instr := S.endpoints
  have hΓL : EffectCtx.Pure ΓL := extended_pure hΓ
  have hΓR : EffectCtx.Pure ΓR := extended_pure hΓ
  have hsL := extended_slots hs x
  have hsR := extended_slots hs y
  have hwl := Flatten.source_wf S hΓL hsL e l hl
  have hwl' := Flatten.source_wf S hΓL hsL e l' hl'
  have hwr := Flatten.source_wf S hΓR hsR e r hr
  have hwr' := Flatten.source_wf S hΓR hsR e r' hr'
  have he := SumSplit.native_specializations (Γ := Γ₊) (X := Ty.base x) (Y := Ty.base y)
    0 (extended_pure hΓ) rfl ht ht' hn
  obtain ⟨⟨_, _, hl₀, hl₁, hnL⟩, ⟨_, _, hr₀, hr₁, hnR⟩⟩ := he
  exact ⟨reflect_arm S hΓL hsL l l' hl hl' hl₀ hl₁
      (specialize_left hwl hwr) (specialize_left hwl' hwr') hnL,
    reflect_arm S hΓR hsR r r' hr hr' hr₀ hr₁
      (specialize_right hwl hwr) (specialize_right hwl' hwr') hnR⟩

public theorem endpoint_reflection (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (l l' : Flatten.Program S (extendSorts x ts) c) (r r' : Flatten.Program S (extendSorts y ts) c)
    (hl : Flatten.Program.WellTyped S e l) (hl' : Flatten.Program.WellTyped S e l')
    (hr : Flatten.Program.WellTyped S e r) (hr' : Flatten.Program.WellTyped S e r')
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : (onHead l.source r.source).toLetIter (Γ.length + 1) = some t)
    (ht' : (onHead l'.source r'.source).toLetIter (Γ.length + 1) = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) (EffectCtx.toBoundCtx Γ₊) t s (.base c) ↔
      Eqv Γ₊ (.base c) e (onHead l.source r.source) (onHead l'.source r'.source) := by
  let instr := S.endpoints
  refine ⟨fun hn => ?_, fun hh => hh.toLetIter ht ht'⟩
  have hΓL : EffectCtx.Pure ΓL := extended_pure hΓ
  have hΓR : EffectCtx.Pure ΓR := extended_pure hΓ
  have hsL := extended_slots hs x
  have hsR := extended_slots hs y
  exact (eqv_iff_arms (Flatten.source_wf S hΓL hsL e l hl) (Flatten.source_wf S hΓR hsR e r hr)
    (Flatten.source_wf S hΓL hsL e l' hl') (Flatten.source_wf S hΓR hsR e r' hr')).mpr
    (arms_eqv_of_native S hΓ hs e l l' r r' hl hl' hr hr' ht ht' hn)

end Reflection

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case.Proofs
