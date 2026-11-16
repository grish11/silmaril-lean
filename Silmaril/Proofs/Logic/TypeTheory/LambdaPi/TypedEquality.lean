module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional.Assignment
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional.Syntax.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.Thms

public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEquality

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional
open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

private theorem under_binder {n : ℕ} {Γ : Context n} {Δ : ECtx} {σ : Fin n → ETm 0}
    {A : Term n} {B b b' : Term (n + 1)} (e : TypedAssignment Γ Δ σ)
    (hΔ : ECtx.JEqH ∅ Δ .unit .star .star)
    (hA : ECtx.JEqH ∅ Δ (.univ 0) (term σ A) (term σ A))
    (ih : ∀ Ξ (τ : Fin (n + 1) → ETm 0), TypedAssignment (Γ.snoc A) Ξ τ →
      ECtx.JEqH ∅ Ξ .unit .star .star → ECtx.JEqH ∅ Ξ (term τ B) (term τ b) (term τ b')) :
    ∀ x ∉ Δ.dv, ECtx.JEqH ∅ (Δ.cons x (term σ A)) ((term (lift σ) B).open x)
      ((term (lift σ) b).open x) ((term (lift σ) b').open x) := by
  intro x hx
  simpa only [term_lift_open] using
    ih _ _ (assignment_cons e hΔ hx hA) (.cons_ok hΔ hx hA)

private theorem family {n j : ℕ} {Γ : Context n} {Δ : ECtx} {σ : Fin n → ETm 0}
    {A : Term n} {B B' : Term (n + 1)} (e : TypedAssignment Γ Δ σ)
    (hΔ : ECtx.JEqH ∅ Δ .unit .star .star)
    (hA : ECtx.JEqH ∅ Δ (.univ 0) (term σ A) (term σ A))
    (ih : ∀ Ξ (τ : Fin (n + 1) → ETm 0), TypedAssignment (Γ.snoc A) Ξ τ →
      ECtx.JEqH ∅ Ξ .unit .star .star → ECtx.JEqH ∅ Ξ (.univ j) (term τ B) (term τ B')) :
    ∀ x ∉ Δ.dv, ECtx.JEqH ∅ (Δ.cons x (term σ A)) (.univ j)
      ((term (lift σ) B).open x) ((term (lift σ) B').open x) := by
  intro x hx
  simpa only [term_lift_open, term] using
    ih _ _ (assignment_cons e hΔ hx hA) (.cons_ok hΔ hx hA)

theorem translate {k n : ℕ} {S : Context k} {Γ : Context n} {t u A : Term n}
    (h : Equality S Γ t u A) : ∀ Δ (σ : Fin n → ETm 0), TypedAssignment Γ Δ σ →
      ECtx.JEqH ∅ Δ .unit .star .star → ECtx.JEqH ∅ Δ (term σ A) (term σ t) (term σ u) := by
  induction h using Equality.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
  case nil => trivial
  case snoc => trivial
  case signature => trivial
  case snoc => intros; trivial
  all_goals intro Δ σ e hΔ
  all_goals try simp only [term, term_instantiate] at *
  case type => exact .univ hΔ
  case var k n S Γ i A hΓ hi ihΓ => exact e hi
  case pi k n S s Γ A A' B B' hA hB ihA ihB =>
    have hAσ : ECtx.JEqH ∅ Δ (.univ 0) (term σ A) (term σ A') := ihA Δ σ e hΔ
    have hAf : ECtx.JEqH ∅ Δ (.univ 0) (term σ A) (term σ A) := ECtx.JEqH.trans hAσ (.symm hAσ)
    exact .pi (.cumul (Nat.zero_le s.val) hAσ) (family e hΔ hAf ihB)
  case lam k n S s Γ A B b b' hA hB hb ihA ihB ihb =>
    have hAσ : ECtx.JEqH ∅ Δ (.univ 0) (term σ A) (term σ A) := ihA Δ σ e hΔ
    exact .abs (.cumul (Nat.zero_le s.val) hAσ) (family e hΔ hAσ ihB)
      (under_binder e hΔ hAσ ihb)
  case app k n S s Γ A f f' a a' B hA hB hf ha ihA ihB ihf iha =>
    have hAσ : ECtx.JEqH ∅ Δ (.univ 0) (term σ A) (term σ A) := ihA Δ σ e hΔ
    exact .app (.cumul (Nat.zero_le s.val) hAσ) (family e hΔ hAσ ihB)
      (ihf Δ σ e hΔ) (iha Δ σ e hΔ)
  case beta k n S s Γ A a B b hA hB hb ha ihA ihB ihb iha =>
    have hAσ : ECtx.JEqH ∅ Δ (.univ 0) (term σ A) (term σ A) := ihA Δ σ e hΔ
    exact .beta_app (.cumul (Nat.zero_le s.val) hAσ) (family e hΔ hAσ ihB)
      (under_binder e hΔ hAσ ihb) (iha Δ σ e hΔ)
  case eta k n S s Γ A f B hA hB hf ihA ihB ihf =>
    have hAσ : ECtx.JEqH ∅ Δ (.univ 0) (term σ A) (term σ A) := ihA Δ σ e hΔ
    have hη : ECtx.JEqH ∅ Δ (.pi (term σ A) (term (lift σ) B))
        (.abs (term σ A) (.app (term σ f).wk0 (.bv 0))) (term σ f) :=
      ECtx.JEqH.function_eta (.cumul (Nat.zero_le s.val) hAσ)
      (family e hΔ hAσ ihB) (ihf Δ σ e hΔ)
    simpa only [Term.weaken, term_rename, Function.comp_def, lift, term,
      Fin.cons_succ, Fin.cons_zero, ETm.wk0, term_wkn] using hη
  case conv k n S s Γ t u A B ht hAB iht ihAB => exact .conv (ihAB Δ σ e hΔ) (iht Δ σ e hΔ)
  case symm k n S Γ t u A h ih => exact .symm (ih Δ σ e hΔ)
  case trans k n S Γ t u v A h h' ih ih' => exact .trans (ih Δ σ e hΔ) (ih' Δ σ e hΔ)

theorem source_context {k n : ℕ} {S : Context k} {Γ : Context n} {t u A : Term n}
    (h : Equality S Γ t u A) : ContextFormed S Γ := by
  induction h using Equality.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
  case nil => trivial
  case snoc => trivial
  case signature => trivial
  case snoc => intros; trivial
  case type k n S Γ hΓ ihΓ => exact hΓ
  case var k n S Γ i A hΓ hi ihΓ => exact hΓ
  case pi k n S s Γ A A' B B' hA hB ihA ihB => exact ihA
  case lam k n S s Γ A B b b' hA hB hb ihA ihB ihb => exact ihA
  case app k n S s Γ A f f' a a' B hA hB hf ha ihA ihB ihf iha => exact ihA
  case beta k n S s Γ A a B b hA hB hb ha ihA ihB ihb iha => exact ihA
  case eta k n S s Γ A f B hA hB hf ihA ihB ihf => exact ihA
  case conv k n S s Γ t u A B ht hAB iht ihAB => exact iht
  case symm k n S Γ t u A h ih => exact ih
  case trans k n S Γ t u v A h h' ih ih' => exact ih

/-- Actual target formation and lookup images for an injectively named telescope. -/
@[expose] def Realizes {n : ℕ} (Γ : Context n) : Prop :=
  ∀ ι : Fin n → String, Function.Injective ι →
    ECtx.JEqH ∅ (context Γ ι) .unit .star .star ∧
      TypedAssignment Γ (context Γ ι) (fun i => .fv (ι i))

private theorem realizes_snoc {n i : ℕ} {Γ : Context n} {A : Term n}
    (hΓ : Realizes Γ)
    (hA : ∀ Δ (σ : Fin n → ETm 0), TypedAssignment Γ Δ σ →
      ECtx.JEqH ∅ Δ .unit .star .star → ECtx.JEqH ∅ Δ (.univ i) (term σ A) (term σ A)) :
    Realizes (Γ.snoc A) := by
  intro ι hι
  have hTail : Function.Injective (ι ∘ Fin.succ) := fun _ _ h => Fin.succ_inj.mp (hι h)
  obtain ⟨hctx, e⟩ := hΓ (fun i => ι i.succ) hTail
  have hAσ := hA _ _ e hctx
  have hx : ι 0 ∉ (context Γ (fun i => ι i.succ)).dv := by
    intro hx
    obtain ⟨i, hi⟩ := context_names Γ (fun i => ι i.succ) (ι 0) hx
    exact Fin.succ_ne_zero i (hι hi)
  have hσ : Fin.cons (.fv (ι 0) : ETm 0) (fun i => ETm.fv (ι i.succ)) =
      (fun i => ETm.fv (ι i)) := by
    funext i
    cases i using Fin.cases <;> rfl
  constructor
  · exact .cons_ok hctx hx hAσ
  · change TypedAssignment (Γ.snoc A)
      ((context Γ (fun i => ι i.succ)).cons (ι 0) (term (fun i => .fv (ι i.succ)) A))
      (fun i => .fv (ι i))
    rw [← hσ]
    exact assignment_cons e hctx hx hAσ

theorem realizes {n : ℕ} (Γ : Context n) :
    (SignatureFormed Γ → Realizes Γ) ∧
      (∀ {k : ℕ} {S : Context k}, ContextFormed S Γ → Realizes Γ) := by
  induction Γ with
  | nil =>
    show (SignatureFormed (.nil : Context 0) → Realizes .nil) ∧
      (∀ {k : ℕ} {S : Context k}, ContextFormed S .nil → Realizes .nil)
    have hnil : Realizes .nil := by
      intro ι hι
      refine ⟨.nil_ok, ?_⟩
      intro i A hi
      cases hi
    exact ⟨fun _ => hnil, fun _ => hnil⟩
  | snoc Γ A ih =>
    show (SignatureFormed (Γ.snoc A) → Realizes (Γ.snoc A)) ∧
      (∀ {k : ℕ} {S : Context k}, ContextFormed S (Γ.snoc A) → Realizes (Γ.snoc A))
    have hs : SignatureFormed (Γ.snoc A) → Realizes (Γ.snoc A) := by
      intro h
      cases h with
      | snoc hS hA =>
        exact realizes_snoc (ih.1 hS) (translate hA)
    constructor
    · exact hs
    · intro k S h
      cases h with
      | signature hS => exact hs hS
      | snoc hΓ hA =>
        show Realizes (Γ.snoc A)
        exact realizes_snoc (ih.2 hΓ) (translate hA)

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEquality
