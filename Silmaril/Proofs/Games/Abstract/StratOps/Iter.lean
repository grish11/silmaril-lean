module

public import Silmaril.Proofs.Games.Abstract.StratOps.Sat

/-!
# Iteration of observation triples preserves admissibility (proofs)

Every call prefix of `iterT t` is, for a saturated body `t`, a pending call of the body after a
finite continuing chain: a prefix inside the chain is a prefix of one of its continuing
iterations (`chain_prefix`), a prefix of a finished iterated behaviour is handled by induction
on `AFun.IterBeh`, and a prefix of an infinite productive chain lies in a finite part of it.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratOps

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A B : Type u} {t : ObsTriple E S A (B ⊕ A)}

/-- A continuing chain extended by one more continuing iteration. -/
theorem contChain_snoc {f : AFun E S A (B ⊕ A)} {s a c s' a' l s'' a''}
    (h : FullFun.ContChain f s a c s' a') (hl : (l, End.ret (.inr a'') s'') ∈ f s' a') :
    FullFun.ContChain f s a (c ++ l) s'' a'' := by
  induction h with
  | refl => simpa using FullFun.ContChain.step hl .refl
  | step h₁ _ ih => rw [List.append_assoc]; exact .step h₁ (ih hl)

/-- A call prefix inside a continuing chain is a call prefix of one of its iterations. -/
theorem chain_prefix {s : S} {a : A} {c s' a'} (h : FullFun.ContChain t.1 s a c s' a')
    {x : List (Call E)} {m : E.Op} (hx : CallPre x m c) :
    ∃ c₀ s₀ a₀ x', FullFun.ContChain t.1 s a c₀ s₀ a₀ ∧ x = c₀ ++ x' ∧
      (x', m) ∈ satP t s₀ a₀ := by
  induction h generalizing x with
  | refl => obtain ⟨_, _, h⟩ := hx; simp at h
  | step h₁ _ ih =>
    rcases callPre_append hx with hx | ⟨c₃, rfl, hc⟩
    · exact ⟨[], _, _, x, .refl, rfl, beh_satP h₁ hx⟩
    · obtain ⟨c₀, s₀, a₀, x', hch, rfl, hm⟩ := ih hc
      exact ⟨_ ++ c₀, s₀, a₀, x', .step h₁ hch, by rw [List.append_assoc], hm⟩

/-- The log of the first `n` iterations of an infinite continuing chain is a continuing
chain. -/
theorem chain_range {σ : Nat → S × A} {l : Nat → List (Call E)}
    (hσ : ∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ t.1 (σ n).1 (σ n).2)
    (n : Nat) :
    FullFun.ContChain t.1 (σ 0).1 (σ 0).2 ((List.range n).flatMap l) (σ n).1 (σ n).2 := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact contChain_snoc ih (hσ n)

variable (ht : Saturated t)
include ht

theorem iterPending_of_chain {s : S} {a : A} {c s₀ a₀} (h : FullFun.ContChain t.1 s a c s₀ a₀)
    {x' : List (Call E)} {m : E.Op} (hm : (x', m) ∈ satP t s₀ a₀) :
    (c ++ x', m) ∈ (iterT t).2.1 s a :=
  ⟨c, s₀, a₀, x', m, h, saturated_iff.1 ht ▸ hm, rfl⟩

theorem iterPending_of_chain_prefix {s : S} {a : A} {c s' a'}
    (h : FullFun.ContChain t.1 s a c s' a') {x : List (Call E)} {m : E.Op}
    (hx : CallPre x m c) : (x, m) ∈ (iterT t).2.1 s a := by
  obtain ⟨c₀, s₀, a₀, x', hch, rfl, hm⟩ := chain_prefix h hx
  exact iterPending_of_chain ht hch hm

theorem iterBeh_prefix {s : S} {a : A} {y : CallBeh E S B} (h : AFun.IterBeh t.1 s a y)
    {x : List (Call E)} {m : E.Op} (hx : CallPre x m y.1) : (x, m) ∈ (iterT t).2.1 s a := by
  induction h generalizing x with
  | exit h₁ => simpa using iterPending_of_chain ht .refl (beh_satP h₁ hx)
  | trap h₁ => simpa using iterPending_of_chain ht .refl (beh_satP h₁ hx)
  | div h₁ => simpa using iterPending_of_chain ht .refl (beh_satP h₁ hx)
  | step h₁ _ ih =>
    rcases callPre_append hx with hx | ⟨c₃, rfl, hc⟩
    · simpa using iterPending_of_chain ht .refl (beh_satP h₁ hx)
    · obtain ⟨c₀, s₀, a₀, x', m', hch, hm, he⟩ := ih hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨_ ++ c₀, s₀, a₀, x', m, .step h₁ hch, hm, by rw [List.append_assoc]⟩
  | spin => obtain ⟨_, _, h⟩ := hx; simp at h

/-- **Iteration preserves admissibility.** -/
theorem saturated_iterT : Saturated (iterT t) := by
  rw [saturated_iff]
  funext s a
  refine le_antisymm ?_ fun _ => .inl
  rintro ⟨x, m⟩ (h | ⟨d, m', hd, hc⟩ | ⟨d, e, hd, hc⟩ | ⟨ω, hω, k, rfl, rfl⟩)
  · exact h
  · obtain ⟨c, s', a', c', m'', hch, hm, he⟩ := hd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rcases callPre_append hc with hc | ⟨c₃, rfl, hc⟩
    · exact iterPending_of_chain_prefix ht hch hc
    · exact iterPending_of_chain ht hch (satP_prefix (.inl hm) hc)
  · exact iterBeh_prefix ht hd hc
  · rcases hω with ⟨c, s', a', ω', hch, hω', rfl⟩ | ⟨σ, l, hσ0, hσ, hcat, hunb⟩
    · rcases Nat.lt_or_ge k c.length with hk | hk
      · rw [streamTake_append_le c ω' hk.le, append_get_lt c ω' hk]
        exact iterPending_of_chain_prefix ht hch (callPre_take hk)
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
        rw [streamTake_append, append_get_ge]
        exact iterPending_of_chain ht hch (stream_satP hω' j)
    · obtain ⟨n, hn⟩ := hunb (k + 1)
      have hk : k < ((List.range n).flatMap l).length := hn
      have hch := chain_range hσ n
      rw [hσ0] at hch
      have htake : streamTake ω k = ((List.range n).flatMap l).take k := by
        apply List.ext_getElem (by simp only [streamTake, List.length_ofFn, List.length_take]; omega)
        intro i h₁ h₂
        simp only [streamTake, List.getElem_ofFn, List.getElem_take]
        exact hcat n i (by simp [streamTake] at h₁; omega)
      rw [htake, hcat n k hk]
      exact iterPending_of_chain_prefix ht hch (callPre_take hk)

end Silmaril.Proofs.Games.Abstract.StratOps
