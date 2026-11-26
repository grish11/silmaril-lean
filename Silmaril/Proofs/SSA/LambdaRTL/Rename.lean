module

public import Silmaril.SSA.LambdaRTL.Nameless.Defs

/-!
# Register renaming invariance of λRTL (proofs)

Restated in `Silmaril.SSA.LambdaRTL.Nameless.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.Rename

open Silmaril.SSA.LambdaRTL

universe v w

variable {V W L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

variable [DecidableEq V] [DecidableEq W]

omit [DecidableEq W] in
theorem Val.eval_rename_on (m : Model F M α) (g : V → W) {S : Set V} {σ : V → α}
    {σ' : W → α} (h : ∀ x ∈ S, σ' (g x) = σ x) :
    ∀ a : Val V, (↑a.fv : Set V) ⊆ S → (a.rename g).eval m σ' = a.eval m σ
  | .var x, ha => h x (ha (by simp [Val.fv]))
  | .unit, _ => rfl
  | .pair a b, ha => by
      simp only [Val.rename, Val.eval,
        Val.eval_rename_on m g h a (fun z hz => ha (by simp [Val.fv, hz])),
        Val.eval_rename_on m g h b (fun z hz => ha (by simp [Val.fv, hz]))]

omit [DecidableEq W] in
theorem Op.eval_rename_on [Monad M] (m : Model F M α) (g : V → W) {S : Set V} {σ : V → α}
    {σ' : W → α} (h : ∀ x ∈ S, σ' (g x) = σ x) (o : Op V F) (ho : (↑o.fv : Set V) ⊆ S) :
    (o.rename g).eval m σ' = o.eval m σ := by
  cases o <;> simp only [Op.rename, Op.eval, Op.fv] at ho ⊢ <;>
    rw [Val.eval_rename_on m g h _ ho]

theorem upd_rename_on {g : V → W} {S : Set V} (hg : Set.InjOn g S) {σ : V → α}
    {σ' : W → α} (h : ∀ x ∈ S, σ' (g x) = σ x) {x : V} (hx : x ∈ S) (a : α) :
    ∀ y ∈ S, upd σ' (g x) a (g y) = upd σ x a y := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simp [upd]
  · have hne : g y ≠ g x := fun e => hyx (hg hy hx e)
    simp only [upd, hne, hyx, ite_false]
    exact h y hy

variable [Monad M] [LawfulMonad M] [DecidableEq L]

/-- Register renaming that is injective on a set `S` of names containing every name the region
uses preserves the store semantics, up to the renaming of the final store on `S`. -/
theorem Region.evalRTL_rename_on (m : Model F M α) {g : V → W} {S : Set V}
    (hg : Set.InjOn g S) {β : Type w} :
    ∀ (r : Region V L F), (↑r.vars : Set V) ⊆ S → ∀ (σ : V → α) (σ' : W → α), (∀ x ∈ S, σ' (g x) = σ x) →
      ∀ (K : L × α × (V → α) → M β) (K' : L × α × (W → α) → M β),
      (∀ l a τ τ', (∀ x ∈ S, τ' (g x) = τ x) → K' (l, a, τ') = K (l, a, τ)) →
      ((r.rename g).evalRTL m σ' >>= K') = (r.evalRTL m σ >>= K)
  | .br ℓ a, hS, σ, σ', h, K, K', hK => by
      simp only [Region.rename, Region.evalRTL, pure_bind,
        Val.eval_rename_on m g h a (by simpa [Region.vars] using hS)]
      exact hK _ _ _ _ h
  | .let1 x o r, hS, σ, σ', h, K, K', hK => by
      have hx : x ∈ S := hS (by simp [Region.vars])
      simp only [Region.rename, Region.evalRTL, bind_assoc,
        Op.eval_rename_on m g h o (fun z hz => hS (by simp [Region.vars, hz]))]
      congr 1; funext a
      exact Region.evalRTL_rename_on m hg r (fun z hz => hS (by simp [Region.vars, hz])) _ _
        (upd_rename_on hg h hx a) K K' hK
  | .let2 x y o r, hS, σ, σ', h, K, K', hK => by
      have hx : x ∈ S := hS (by simp [Region.vars])
      have hy : y ∈ S := hS (by simp [Region.vars])
      simp only [Region.rename, Region.evalRTL, bind_assoc,
        Op.eval_rename_on m g h o (fun z hz => hS (by simp [Region.vars, hz]))]
      congr 1; funext a; congr 1; funext p
      exact Region.evalRTL_rename_on m hg r (fun z hz => hS (by simp [Region.vars, hz])) _ _
        (upd_rename_on hg (upd_rename_on hg h hx p.1) hy p.2) K K' hK
  | .case o x r y s, hS, σ, σ', h, K, K', hK => by
      have hx : x ∈ S := hS (by simp [Region.vars])
      have hy : y ∈ S := hS (by simp [Region.vars])
      simp only [Region.rename, Region.evalRTL, bind_assoc,
        Op.eval_rename_on m g h o (fun z hz => hS (by simp [Region.vars, hz]))]
      congr 1; funext a; congr 1; funext c
      have hr : (↑r.vars : Set V) ⊆ S := fun z hz => hS (by simp [Region.vars, hz])
      have hs : (↑s.vars : Set V) ⊆ S := fun z hz => hS (by simp [Region.vars, hz])
      cases c with
      | inl b => exact Region.evalRTL_rename_on m hg r hr _ _ (upd_rename_on hg h hx b) K K' hK
      | inr b => exact Region.evalRTL_rename_on m hg s hs _ _ (upd_rename_on hg h hy b) K K' hK
  | .join r ℓ x t, hS, σ, σ', h, K, K', hK => by
      have hx : x ∈ S := hS (by simp [Region.vars])
      simp only [Region.rename, Region.evalRTL, bind_assoc]
      apply Region.evalRTL_rename_on m hg r (fun z hz => hS (by simp [Region.vars, hz])) σ σ' h
      intro l a τ τ' hτ
      dsimp only
      split
      · exact Region.evalRTL_rename_on m hg t (fun z hz => hS (by simp [Region.vars, hz])) _ _
          (upd_rename_on hg hτ hx a) K K' hK
      · simp only [pure_bind]; exact hK _ _ _ _ hτ

theorem Region.evalObs_rename_on (m : Model F M α) {g : V → W} {S : Set V}
    (hg : Set.InjOn g S) (r : Region V L F) (hS : (↑r.vars : Set V) ⊆ S) {σ : V → α} {σ' : W → α}
    (h : ∀ x ∈ S, σ' (g x) = σ x) : (r.rename g).evalObs m σ' = r.evalObs m σ := by
  simp only [Region.evalObs, map_eq_pure_bind]
  exact Region.evalRTL_rename_on m hg r hS σ σ' h _ _ (fun _ _ _ _ _ => rfl)

/-- Global injectivity is the instance with every register in the support. -/
theorem Region.evalRTL_rename (m : Model F M α) {f : V → W} (hf : Function.Injective f)
    {β : Type w} (r : Region V L F) (σ : V → α) (σ' : W → α) (h : ∀ x, σ' (f x) = σ x)
    (K : L × α × (V → α) → M β) (K' : L × α × (W → α) → M β)
    (hK : ∀ l a τ τ', (∀ x, τ' (f x) = τ x) → K' (l, a, τ') = K (l, a, τ)) :
    ((r.rename f).evalRTL m σ' >>= K') = (r.evalRTL m σ >>= K) :=
  Region.evalRTL_rename_on m hf.injOn r (Set.subset_univ _) σ σ' (fun x _ => h x)
    K K' (fun l a τ τ' hτ => hK l a τ τ' (fun x => hτ x (Set.mem_univ x)))

theorem Region.evalObs_rename (m : Model F M α) {f : V → W} (hf : Function.Injective f)
    (r : Region V L F) {σ : V → α} {σ' : W → α} (h : ∀ x, σ' (f x) = σ x) :
    (r.rename f).evalObs m σ' = r.evalObs m σ :=
  Region.evalObs_rename_on m hf.injOn r (Set.subset_univ _) (fun x _ => h x)

end Silmaril.Proofs.SSA.LambdaRTL.Rename
