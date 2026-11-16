module

public import Silmaril.Games.Abstract.FunctionIter.Defs

/-!
# The fixpoint law for iteration of abstract functions (proofs)

`iter_unfold`: `iter f = seq f (case pure (iter f))`. Each constructor of `AFun.IterBeh` is
one iteration followed by the rest: `exit` is a return `inl b` followed by `pure`, `trap` and
`div` end the first iteration, `step` is a return `inr a'` followed by the iterated behaviour,
and an infinite silent chain is its first silent iteration followed by the shifted chain.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FunctionIter

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.AFun

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- **The fixpoint law** for iteration. -/
theorem iter_unfold (f : AFun E S A (B ⊕ A)) : iter f = seq f (case pure (iter f)) := by
  funext s a
  ext x
  simp only [iter, AFun.seq, Set.mem_ofPred_eq]
  constructor
  · intro hx
    cases hx with
    | exit hm => exact .inr (.inr ⟨_, _, _, [], _, hm, rfl, by rw [List.append_nil]⟩)
    | trap hm => exact .inl ⟨_, hm, rfl⟩
    | div hm => exact .inr (.inl ⟨_, hm, rfl⟩)
    | step hm hr => exact .inr (.inr ⟨_, _, _, _, _, hm, hr, rfl⟩)
    | spin σ h0 hσ =>
      have h1 := hσ 0
      rw [h0] at h1
      exact .inr (.inr ⟨[], _, _, [], _, h1,
        IterBeh.spin (fun n => σ (n + 1)) rfl fun n => hσ (n + 1), rfl⟩)
  · rintro (⟨c, hm, rfl⟩ | ⟨c, hm, rfl⟩ | ⟨c₁, b | a', s₁, c₂, e, hm, hk, rfl⟩)
    · exact .trap hm
    · exact .div hm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      rw [List.append_nil]
      exact .exit hm
    · exact .step hm hk

end Silmaril.Proofs.Games.Abstract.FunctionIter
