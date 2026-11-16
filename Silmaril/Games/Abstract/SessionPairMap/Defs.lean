module

public import Silmaril.Games.Abstract.SessionPair.Defs
import Silmaril.Proofs.Games.Abstract.SessionPairMap.Pos

/-!
# Relabelling the pairing of two sessions

`relabelPair σ : DStrategy E (sig1 (A₁ ⊕ A₂) (B₁ ⊕ B₂))` is a divergence-observing strategy
`σ : DStrategy E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)` relabelled along `StratSession.pairMove`: its plays,
divergences and infinite plays are the images of those of `σ`. The two interfaces have the same
questions; only answers change, injectively, so Opponent moves have preimages and receptiveness
transfers.

For triples without plain traps, the session of the paired triple is the relabelled pairing of
the two sessions (`Silmaril.Games.Abstract.SessionPairMap.Thms`).
-/

@[expose] public section

namespace Silmaril.Games.Abstract.StratSession

open Silmaril.Games
open Silmaril.Proofs.Games.Abstract.SessionPairMap (posMap path_map)

universe u

variable {E : Sig.{u}} {A₁ A₂ B₁ B₂ : Type u}

/-- The image of an infinite trace along `pairMove`. -/
theorem isInfPlay_image_pairMove {I : Set (List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)))}
    (hI : IsInfPlay I) : IsInfPlay (List.map pairMove '' I) where
  of_prefix := by
    rintro s _ ⟨t, ht, rfl⟩ hs
    refine ⟨t.take s.length, hI.of_prefix ht (List.take_prefix _ _), ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hs).symm
  total := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    rcases hI.total hs ht with h | h
    · exact .inl (h.map _)
    · exact .inr (h.map _)
  unbounded k := by
    obtain ⟨s, hs, hk⟩ := hI.unbounded k
    exact ⟨_, ⟨s, hs, rfl⟩, by simpa using hk⟩

/-- **Relabel the pairing of two sessions** along `pairMove`: plays, divergences and infinite plays
are the images. -/
def relabelPair (σ : DStrategy E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)) :
    DStrategy E (sig1 (A₁ ⊕ A₂) (B₁ ⊕ B₂)) where
  toStrategy :=
    { plays := {p | ∃ q ∈ σ.toStrategy.plays, q.map pairMove = p}
      nil_mem := ⟨[], σ.toStrategy.nil_mem, rfl⟩
      legal := by
        rintro _ ⟨q, hq, rfl⟩
        obtain ⟨y, hy⟩ := σ.toStrategy.legal hq
        exact ⟨_, path_map hy⟩
      of_prefix := by
        rintro s _ ⟨q, hq, rfl⟩ hs
        refine ⟨q.take s.length, σ.toStrategy.of_prefix hq (List.take_prefix _ _), ?_⟩
        rw [List.map_take]
        exact (List.prefix_iff_eq_take.1 hs).symm
      receptive := by
        rintro _ x y o ⟨q, hq, rfl⟩ hx hs ho
        obtain ⟨x₀, hx₀⟩ := σ.toStrategy.legal hq
        have hxx : posMap x₀ = x := Path.det (path_map hx₀) hx
        cases hs with
        | ask a =>
          cases x₀ <;> simp [posMap] at hxx
          exact ⟨_, σ.toStrategy.receptive hq hx₀
            (Step.ask (E := E) (F := sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂) a) trivial, by simp; rfl⟩
        | reply a m n =>
          cases x₀ <;> simp [posMap] at hxx
          obtain ⟨rfl, rfl⟩ := hxx
          exact ⟨_, σ.toStrategy.receptive hq hx₀
            (Step.reply (E := E) (F := sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂) _ _ n) trivial, by simp; rfl⟩
        | call => simp [Move.IsO] at ho
        | ret => simp [Move.IsO] at ho }
  div := {p | ∃ q ∈ σ.div, q.map pairMove = p}
  inf := {K | ∃ J ∈ σ.inf, K = List.map pairMove '' J}
  div_mem := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q, σ.div_mem hq, rfl⟩
  div_run := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨a, ha⟩ := σ.div_run hq
    exact ⟨a, path_map ha⟩
  inf_isInf := by
    rintro _ ⟨J, hJ, rfl⟩
    exact isInfPlay_image_pairMove (σ.inf_isInf hJ)
  inf_sub := by
    rintro _ ⟨J, hJ, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨q, σ.inf_sub hJ hq, rfl⟩

end Silmaril.Games.Abstract.StratSession
