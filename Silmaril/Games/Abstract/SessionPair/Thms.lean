module

public import Silmaril.Games.Abstract.SessionPair.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Games.DPair.Defs
import Silmaril.Proofs.Games.Abstract.SessionPair.Basic
import Silmaril.Proofs.Games.Abstract.SessionPair.Plays

/-!
# Pairing sessions: theorems

**The paired triple.** A round on `.inl a₁` is a round of `t₁` on the first store
(`mem_pairS_inl`), with the call prefixes of `t₁` (`satP_pairS_inl`); symmetrically on the right.

**Coherence.** Pairing preserves the absence of plain traps (`noPlainTrap_pairS`), store
determinism (`storeDet_pairS`) and determinism given answers (`det_pairS`).

**The session of the paired triple is the pairing of the sessions.** For triples without plain
traps, `threadS (pairS t₁ t₂) (s₁, s₂)` and `(threadS t₁ s₁).pair (threadS t₂ s₂)` correspond
along the injective relabelling `pairMove` (`pairMove_injective`):

* finite plays: `q` is a play of the pairing iff `q.map pairMove` is a play of the paired session
  (`mem_pair_threadS_iff`), and every play of the paired session is a relabelled play
  (`exists_map_pairMove`);
* divergence: `q` diverges in the pairing iff `q.map pairMove` diverges in the paired session
  (`mem_div_pair_threadS_iff`).

The proof relates the threading automata (`StratThread.TSt`): the paired automaton is idle at
`(s₁, s₂)` when both components are idle at `s₁` and `s₂`, and runs a left question when the left
component runs it, the right one idle; runs of the paired automaton split into runs of the
components on the halves (`Split.halves`) of a play, and conversely for legal plays.
`NoPlainTrap` is needed: a plain trap of `t₁` ends the session of `t₁` but not that of `t₂` in
the pairing, while it ends the whole paired session.

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
    x ∈ (pairS t₁ t₂).1 σ (.inl a) ↔ ∃ e, (x.1, e) ∈ t₁.1 σ.1 a ∧ x.2 = pairEndL σ.2 e :=
  Silmaril.Proofs.Games.Abstract.SessionPair.mem_pairS_inl

/-- A right round of the paired triple is a round of `t₂`, keeping the first store. -/
theorem mem_pairS_inr {σ : S₁ × S₂} {a : A₂}
    {x : List (Call E) × End (S₁ × S₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1})} :
    x ∈ (pairS t₁ t₂).1 σ (.inr a) ↔ ∃ e, (x.1, e) ∈ t₂.1 σ.2 a ∧ x.2 = pairEndR σ.1 e :=
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

/-! ## The session of the paired triple -/

variable {s₁ : S₁} {s₂ : S₂}

/-- The relabelling of the pairing of two sessions is injective. -/
theorem pairMove_injective :
    Function.Injective (pairMove (E := E) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)) :=
  Silmaril.Proofs.Games.Abstract.SessionPair.pairMove_injective

/-- **The finite plays of the pairing of two sessions** are the relabelled plays of the paired
session. -/
theorem mem_pair_threadS_iff (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂)
    {q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} :
    q ∈ ((threadS t₁ s₁).pair (threadS t₂ s₂)).toStrategy ↔
      q.map pairMove ∈ (threadS (pairS t₁ t₂) (s₁, s₂)).toStrategy :=
  Silmaril.Proofs.Games.Abstract.SessionPair.mem_pair_iff h₁ h₂

/-- Every play of the paired session is a relabelled play. -/
theorem exists_map_pairMove {p : List (Move E (sig1 (A₁ ⊕ A₂) (B₁ ⊕ B₂)))}
    (hp : p ∈ (threadS (pairS t₁ t₂) (s₁, s₂)).toStrategy) :
    ∃ q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)), q.map pairMove = p :=
  Silmaril.Proofs.Games.Abstract.SessionPair.exists_map_pairMove hp

/-- **The divergent plays of the pairing of two sessions** are the relabelled divergent plays of
the paired session. -/
theorem mem_div_pair_threadS_iff (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂)
    {q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} :
    q ∈ ((threadS t₁ s₁).pair (threadS t₂ s₂)).div ↔
      q.map pairMove ∈ (threadS (pairS t₁ t₂) (s₁, s₂)).div :=
  Silmaril.Proofs.Games.Abstract.SessionPair.mem_div_pair_iff h₁ h₂

end Silmaril.Games.Abstract.StratSession
