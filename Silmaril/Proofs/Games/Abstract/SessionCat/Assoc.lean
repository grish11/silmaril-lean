module

public import Silmaril.Proofs.Games.Abstract.SessionCat.Det
public import Silmaril.Games.DivComp.Thms

/-!
# Session-level category laws: associativity (proofs)

Both bracketings of three linked sessions are, by `comp_threadS`, bracketings of the composite
of the three session strategies, which agree by `DStrategy.comp_assoc`. The hypotheses of the
four uses of `comp_threadS` follow from `NoPlainTrap` of the two servers and `RetDet` of the
three components (`retDet_linkS`, `storeDet_of_retDet`, `noPlainTrap_linkS`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionCat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}} {S₁ S₂ S₃ A B A' B' A'' B'' : Type u}
  {t : ObsTriple E S₁ A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S₂ A' (B' ⊕ PUnit.{u + 1})}
  {v : ObsTriple (sig1 A' B') S₃ A'' (B'' ⊕ PUnit.{u + 1})}

theorem threadS_linkS_assoc (hnt : NoPlainTrap t) (hnu : NoPlainTrap u) (ht : RetDet t)
    (hu : RetDet u) (hv : RetDet v) (s₁ : S₁) (s₂ : S₂) (s₃ : S₃) :
    threadS (linkS (linkS t u) v) ((s₁, s₂), s₃) = threadS (linkS t (linkS u v)) (s₁, (s₂, s₃)) := by
  have htu := retDet_linkS ht hu
  have huv := retDet_linkS hu hv
  rw [← comp_threadS (noPlainTrap_linkS hnu) (storeDet_of_retDet htu)
      (storeDet_of_retDet (retDet_linkS htu hv)),
    ← comp_threadS hnt (storeDet_of_retDet ht) (storeDet_of_retDet htu), DStrategy.comp_assoc,
    comp_threadS hnu (storeDet_of_retDet hu) (storeDet_of_retDet huv),
    comp_threadS hnt (storeDet_of_retDet ht) (storeDet_of_retDet (retDet_linkS ht huv))]

theorem obsEq_linkS_assoc (hnt : NoPlainTrap t) (hnu : NoPlainTrap u) (hnv : NoPlainTrap v)
    (ht : RetDet t) (hu : RetDet u) (hv : RetDet v) (s₁ : S₁) (s₂ : S₂) (s₃ : S₃) :
    ObsEq (linkS (linkS t u) v) (linkS t (linkS u v)) ((s₁, s₂), s₃) (s₁, (s₂, s₃)) :=
  (threadS_eq_iff (storeDet_of_retDet (retDet_linkS (retDet_linkS ht hu) hv))
      (storeDet_of_retDet (retDet_linkS ht (retDet_linkS hu hv))) (noPlainTrap_linkS hnv)
      (noPlainTrap_linkS (noPlainTrap_linkS hnv))).1
    (threadS_linkS_assoc hnt hnu ht hu hv s₁ s₂ s₃)

end Silmaril.Proofs.Games.Abstract.SessionCat
