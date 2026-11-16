module

public import Silmaril.Games.Abstract.SessionPairMap.Defs
public import Silmaril.Games.Abstract.SessionPair.Thms

/-!
# Relabelling the pairing of two sessions: the session of the paired triple

`threadS_pairS`: the three correspondences (`mem_pair_threadS_iff`, `mem_div_pair_threadS_iff`,
`mem_inf_pair_threadS_iff`) and their surjectivity (`exists_map_pairMove`,
`exists_image_pairMove`) give equality with the relabelled pairing.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionPairMap

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}} {S₁ S₂ A₁ A₂ B₁ B₂ : Type u}

theorem threadS_pairS {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})}
    {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})} (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂)
    (s₁ : S₁) (s₂ : S₂) :
    threadS (pairS t₁ t₂) (s₁, s₂) = relabelPair ((threadS t₁ s₁).pair (threadS t₂ s₂)) := by
  refine DStrategy.ext (Strategy.ext fun p => ⟨fun hp => ?_, ?_⟩)
    (Set.ext fun p => ⟨fun hp => ?_, ?_⟩) (Set.ext fun K => ⟨fun hK => ?_, ?_⟩)
  · obtain ⟨q, rfl⟩ := exists_map_pairMove hp
    exact ⟨q, (mem_pair_threadS_iff h₁ h₂).2 hp, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact (mem_pair_threadS_iff h₁ h₂).1 hq
  · obtain ⟨q, rfl⟩ := exists_map_pairMove ((threadS (pairS t₁ t₂) (s₁, s₂)).div_mem hp)
    exact ⟨q, (mem_div_pair_threadS_iff h₁ h₂).2 hp, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact (mem_div_pair_threadS_iff h₁ h₂).1 hq
  · obtain ⟨J, rfl⟩ := exists_image_pairMove hK
    exact ⟨J, (mem_inf_pair_threadS_iff h₁ h₂).2 hK, rfl⟩
  · rintro ⟨J, hJ, rfl⟩
    exact (mem_inf_pair_threadS_iff h₁ h₂).1 hJ

end Silmaril.Proofs.Games.Abstract.SessionPairMap
