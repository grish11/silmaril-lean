module

public import Silmaril.Games.Abstract.SessionPair.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
import Silmaril.Proofs.Games.Abstract.SessionPair.Basic

/-!
# Pairing sessions: theorems

**The paired triple.** A round on `.inl a₁` is a round of `t₁` on the first store
(`mem_pairS_inl`), with the call prefixes of `t₁` (`satP_pairS_inl`); symmetrically on the right.

**Coherence.** Pairing preserves the absence of plain traps (`noPlainTrap_pairS`), store
determinism (`storeDet_pairS`) and determinism given answers (`det_pairS`).

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionPair`.
-/

public section

namespace Silmaril.Games.Abstract.StratSession

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread

universe u

variable {E : Sig.{u}} {S₁ S₂ A₁ A₂ B₁ B₂ : Type u}
  {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})} {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})}

/-! ## The paired triple -/

/-- A left round of the paired triple is a round of `t₁`, keeping the second store. -/
theorem mem_pairS_inl {σ : S₁ × S₂} {a : A₁}
    {x : List (Call E) × End (S₁ × S₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1})} :
    x ∈ (pairS t₁ t₂).1 σ (.inl a) ↔ ∃ e, (x.1, e) ∈ t₁.1 σ.1 a ∧ x.2 = endL σ.2 e :=
  Silmaril.Proofs.Games.Abstract.SessionPair.mem_pairS_inl

/-- A right round of the paired triple is a round of `t₂`, keeping the first store. -/
theorem mem_pairS_inr {σ : S₁ × S₂} {a : A₂}
    {x : List (Call E) × End (S₁ × S₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1})} :
    x ∈ (pairS t₁ t₂).1 σ (.inr a) ↔ ∃ e, (x.1, e) ∈ t₂.1 σ.2 a ∧ x.2 = endR σ.1 e :=
  Silmaril.Proofs.Games.Abstract.SessionPair.mem_pairS_inr

/-- The call prefixes of a left round are those of `t₁`. -/
theorem satP_pairS_inl (σ : S₁ × S₂) (a : A₁) :
    satP (pairS t₁ t₂) σ (.inl a) = satP t₁ σ.1 a :=
  Silmaril.Proofs.Games.Abstract.SessionPair.satP_pairS_inl σ a

/-- The call prefixes of a right round are those of `t₂`. -/
theorem satP_pairS_inr (σ : S₁ × S₂) (a : A₂) :
    satP (pairS t₁ t₂) σ (.inr a) = satP t₂ σ.2 a :=
  Silmaril.Proofs.Games.Abstract.SessionPair.satP_pairS_inr σ a

/-! ## Coherence -/

/-- **Pairing triples without plain traps gives a triple without plain traps.** -/
theorem noPlainTrap_pairS (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂) :
    NoPlainTrap (pairS t₁ t₂) :=
  Silmaril.Proofs.Games.Abstract.SessionPair.noPlainTrap_pairS h₁ h₂

/-- **Pairing preserves store determinism.** -/
theorem storeDet_pairS (h₁ : StoreDet t₁) (h₂ : StoreDet t₂) : StoreDet (pairS t₁ t₂) :=
  Silmaril.Proofs.Games.Abstract.SessionPair.storeDet_pairS h₁ h₂

/-- **Pairing preserves determinism given answers.** -/
theorem det_pairS (h₁ : AFun.Det t₁.1) (h₂ : AFun.Det t₂.1) : AFun.Det (pairS t₁ t₂).1 :=
  Silmaril.Proofs.Games.Abstract.SessionPair.det_pairS h₁ h₂

end Silmaril.Games.Abstract.StratSession
