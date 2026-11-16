module

public import Silmaril.Games.Abstract.FunctionIter.Defs

/-!
# Iteration of abstract functions: proofs

Iteration is monotone, and trap ≈ divergence is a congruence for it: each
constructor of `IterBeh` is matched by one with the same collapsed
observation, and a silent chain only uses returns, which the collapse keeps.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FunctionIter

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.AFun

universe u

variable {E : Sig.{u}} {S A B : Type u}

theorem iter_mono {f g : AFun E S A (B ⊕ A)} (h : f ≤ g) : iter f ≤ iter g := by
  intro s a x hx
  change IterBeh f s a x at hx
  change IterBeh g s a x
  induction hx with
  | exit hm => exact IterBeh.exit (h _ _ hm)
  | trap hm => exact IterBeh.trap (h _ _ hm)
  | div hm => exact IterBeh.div (h _ _ hm)
  | step hm _ ih => exact IterBeh.step (h _ _ hm) ih
  | spin σ h0 hσ => exact IterBeh.spin σ h0 fun n => h _ _ (hσ n)

theorem collapse_eq_ret {S B : Type u} {e : End S B} {b : B} {s : S}
    (h : e.collapse = .ret b s) : e = .ret b s := by
  cases e <;> simp_all [End.collapse]

theorem collapse_eq_abort {S B : Type u} {e : End S B} (h : e.collapse = .abort) :
    e = .trap ∨ e = .div := by
  cases e <;> simp_all [End.collapse]

theorem iter_collapse_sub {f g : AFun E S A (B ⊕ A)}
    (h : ∀ s a, obsCollapse '' f s a ⊆ obsCollapse '' g s a) (s : S) (a : A) :
    obsCollapse '' iter f s a ⊆ obsCollapse '' iter g s a := by
  rintro _ ⟨x, hx, rfl⟩
  change IterBeh f s a x at hx
  induction hx with
  | @exit s a c b s' hm =>
    obtain ⟨⟨c', e'⟩, hm', he⟩ := h s a ⟨_, hm, rfl⟩
    simp only [obsCollapse, Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    obtain rfl := collapse_eq_ret he
    exact ⟨_, IterBeh.exit hm', rfl⟩
  | @trap s a c hm =>
    obtain ⟨⟨c', e'⟩, hm', he⟩ := h s a ⟨_, hm, rfl⟩
    simp only [obsCollapse, Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rcases collapse_eq_abort he with rfl | rfl
    · exact ⟨_, IterBeh.trap hm', rfl⟩
    · exact ⟨_, IterBeh.div hm', rfl⟩
  | @div s a c hm =>
    obtain ⟨⟨c', e'⟩, hm', he⟩ := h s a ⟨_, hm, rfl⟩
    simp only [obsCollapse, Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rcases collapse_eq_abort he with rfl | rfl
    · exact ⟨_, IterBeh.trap hm', rfl⟩
    · exact ⟨_, IterBeh.div hm', rfl⟩
  | @step s a c₁ a' s' c₂ e hm _ ih =>
    obtain ⟨⟨c', e'⟩, hm', he⟩ := h s a ⟨_, hm, rfl⟩
    simp only [obsCollapse, Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    obtain rfl := collapse_eq_ret he
    obtain ⟨⟨c₂', e₂'⟩, hx', he₂⟩ := ih
    simp only [obsCollapse, Prod.mk.injEq] at he₂
    obtain ⟨rfl, he₂⟩ := he₂
    exact ⟨_, IterBeh.step hm' hx', by simp [obsCollapse, he₂]⟩
  | @spin s a σ h0 hσ =>
    refine ⟨_, IterBeh.spin σ h0 fun n => ?_, rfl⟩
    obtain ⟨⟨c', e'⟩, hm', he⟩ := h _ _ ⟨_, hσ n, rfl⟩
    simp only [obsCollapse, Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    obtain rfl := collapse_eq_ret he
    exact hm'

theorem iter_obsCollapse {f g : AFun E S A (B ⊕ A)} (h : ObsEquiv obsCollapse f g) :
    ObsEquiv obsCollapse (iter f) (iter g) := fun s a =>
  (iter_collapse_sub (fun s a => (h s a).le) s a).antisymm
    (iter_collapse_sub (fun s a => (h s a).ge) s a)

theorem iter_continue {f : AFun E S A (B ⊕ A)} (hf : ∀ s a, f s a = {([], .ret (.inr a) s)})
    (s : S) (a : A) : iter f s a = {([], .div)} := by
  ext x
  constructor
  · intro hx
    change IterBeh f s a x at hx
    induction hx with
    | exit hm => rw [hf] at hm; simp at hm
    | trap hm => rw [hf] at hm; simp at hm
    | div hm => rw [hf] at hm; simp at hm
    | step hm _ ih =>
      rw [hf] at hm
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hm ih ⊢
      obtain ⟨rfl, -⟩ := hm
      obtain ⟨rfl, rfl⟩ := ih
      exact ⟨rfl, rfl⟩
    | spin => rfl
  · rintro rfl
    exact IterBeh.spin (fun _ => (s, a)) rfl fun _ => by rw [hf]; rfl

theorem iter_trap {f : AFun E S A (B ⊕ A)} (hf : ∀ s a, f s a = {([], .trap)})
    (s : S) (a : A) : iter f s a = {([], .trap)} := by
  ext x
  constructor
  · intro hx
    change IterBeh f s a x at hx
    induction hx with
    | exit hm => rw [hf] at hm; simp at hm
    | trap hm => rw [hf] at hm; simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hm; rw [hm.1]; rfl
    | div hm => rw [hf] at hm; simp at hm
    | step hm => rw [hf] at hm; simp at hm
    | spin σ _ hσ => have := hσ 0; rw [hf] at this; simp at this
  · rintro rfl
    exact IterBeh.trap (by rw [hf]; rfl)

theorem iter_productive {f : AFun E S A (B ⊕ A)}
    (hf : ∀ s a x, x ∈ f s a → x.1 ≠ [] ∧ ∃ a' s', x.2 = .ret (.inr a') s') (s : S) (a : A) :
    iter f s a = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  change IterBeh f s a x at hx
  induction hx with
  | exit hm => obtain ⟨-, _, _, h⟩ := hf _ _ _ hm; cases h
  | trap hm => obtain ⟨-, _, _, h⟩ := hf _ _ _ hm; cases h
  | div hm => obtain ⟨-, _, _, h⟩ := hf _ _ _ hm; cases h
  | step _ _ ih => exact ih
  | spin σ _ hσ => exact (hf _ _ _ (hσ 0)).1 rfl

end Silmaril.Proofs.Games.Abstract.FunctionIter
