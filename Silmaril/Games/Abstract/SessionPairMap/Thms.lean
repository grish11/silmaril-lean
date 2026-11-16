module

public import Silmaril.Games.Abstract.SessionPairMap.Defs
public import Silmaril.Games.Abstract.SessionPair.Thms
import Silmaril.Proofs.Games.Abstract.SessionPairMap.Eq

/-!
# Relabelling the pairing of two sessions: theorems

**The session of the paired triple is the relabelled pairing of the sessions**
(`threadS_pairS`): for triples without plain traps,

  `threadS (pairS t₁ t₂) (s₁, s₂) = relabelPair ((threadS t₁ s₁).pair (threadS t₂ s₂))`,

in all three components. It combines the correspondences of
`Silmaril.Games.Abstract.SessionPair.Thms` for finite plays, divergence and infinite plays with
their surjectivity.

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionPairMap`.
-/

public section

namespace Silmaril.Games.Abstract.StratSession

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S₁ S₂ A₁ A₂ B₁ B₂ : Type u}

/-- **The session of the paired triple is the relabelled pairing of the sessions.** -/
theorem threadS_pairS {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})}
    {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})} (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂)
    (s₁ : S₁) (s₂ : S₂) :
    threadS (pairS t₁ t₂) (s₁, s₂) = relabelPair ((threadS t₁ s₁).pair (threadS t₂ s₂)) :=
  Silmaril.Proofs.Games.Abstract.SessionPairMap.threadS_pairS h₁ h₂ s₁ s₂

end Silmaril.Games.Abstract.StratSession
