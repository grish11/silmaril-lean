module

public import Silmaril.Games.AnsPull.Defs
public import Silmaril.Games.AnsMap.Thms
public import Silmaril.Games.DPair.Defs
public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.DivLTS.Defs
import Silmaril.Proofs.Games.AnsPull.Laws

/-!
# Relabelling answers below a strategy: theorems

**Composing with the relabelling handler below is pulling back** (`ofHandler_ansH_comp`): for
`τ : DStrategy ⟨E.Op, B'⟩ G` and `k q : E.Ar q → B' q`,

  `(DStrategy.ofHandler (ansH k)).comp τ = τ.pullAns k`,

in all three components. This is the lower counterpart of `DStrategy.comp_ansH` (relabelling
above is `mapAns`). The handler never diverges and makes one visible move per hidden move, so
there is no hidden chatter.

**Pairing** (`pull_pair`): a move map acting on the halves of a pairing pulls the pairing back to
the pairing of the pullbacks. Hence:

* `ofHandler_ansH_comp_pair`: a relabelling handler below a pairing distributes over it, the
  `DStrategy` analogue of `Strategy.ofHandler_comp_pair` for relabelling handlers;
* `mapAns_pair`: invertible relabellings above the two components are the side-by-side
  relabelling (`sumAns`) above the pairing, the analogue of `Strategy.pair_comp_sumMap`
  (`mapAns_eq_pull`: an invertible relabelling is the pullback along its inverse).

**Handler composition** (`ofHandler_ansH_comp_ofHandler`, `ofHandler_comp_ansH`): a relabelling
handler below a handler, or an invertible one above it, composes as handlers do
(`Handler.comp`); both sides are divergence-free with every limit of their plays
(`pull_limits`).

**Inverse relabellings cancel** (`ofHandler_ansH_comp_ansH`): relabelling along `k` then back
along a left inverse `k'` is copycat. So relabelling the hidden middle interface of a composite
changes nothing (`comp_ansH_comp_ansH_comp`):

  `(σ.comp (ofHandler (ansH k))).comp ((ofHandler (ansH k')).comp τ) = σ.comp τ`.

Proofs are in `Silmaril.Proofs.Games.AnsPull`.
-/

public section

namespace Silmaril.Games

universe u

namespace DStrategy

variable {E F G : Sig.{u}}

/-- **Pulling back the divergence-free reading with every limit** is that reading of the
pullback. -/
theorem pull_limits {E' F' : Sig.{u}} {f : Move E F → Move E' F'} {pf : Pos E F → Pos E' F'}
    (hf : PullData f pf) (σ : Strategy E' F') :
    (limits σ).pull f pf hf = limits (σ.pull f pf hf) :=
  Silmaril.Proofs.Games.AnsPull.pull_limits hf σ

/-- **Pulling back a pairing** along a move map acting on halves is pairing the pullbacks. -/
theorem pull_pair {E' F₁ F₂ F₁' F₂' : Sig.{u}} {f : Move E (F₁ ⊕ₛ F₂) → Move E' (F₁' ⊕ₛ F₂')}
    {pf : Pos E (F₁ ⊕ₛ F₂) → Pos E' (F₁' ⊕ₛ F₂')} {f₁ : Move E F₁ → Move E' F₁'}
    {pf₁ : Pos E F₁ → Pos E' F₁'} {f₂ : Move E F₂ → Move E' F₂'} {pf₂ : Pos E F₂ → Pos E' F₂'}
    (hf : PullData f pf) (hf₁ : PullData f₁ pf₁) (hf₂ : PullData f₂ pf₂)
    (hh : ∀ p, Split.halves false (p.map f) =
      ((Split.halves false p).1.map f₁, (Split.halves false p).2.map f₂))
    (σ₁ : DStrategy E' F₁') (σ₂ : DStrategy E' F₂') :
    (σ₁.pair σ₂).pull f pf hf = (σ₁.pull f₁ pf₁ hf₁).pair (σ₂.pull f₂ pf₂ hf₂) :=
  Silmaril.Proofs.Games.AnsPull.pull_pair hf hf₁ hf₂ hh σ₁ σ₂

section Below

variable {B' : E.Op → Type u} {k : (q : E.Op) → E.Ar q → B' q}

/-- **Composing with the relabelling handler below is pulling back.** -/
theorem ofHandler_ansH_comp (τ : DStrategy (Sig.mk E.Op B') G) :
    (DStrategy.ofHandler (ansH k)).comp τ = τ.pullAns k :=
  Silmaril.Proofs.Games.AnsPull.ofHandler_ansH_comp τ

/-- Relabelling below distributes over pairing. -/
theorem pullAns_pair {F₁ F₂ : Sig.{u}} (σ₁ : DStrategy (Sig.mk E.Op B') F₁)
    (σ₂ : DStrategy (Sig.mk E.Op B') F₂) :
    (σ₁.pair σ₂).pullAns k = (σ₁.pullAns k).pair (σ₂.pullAns k) :=
  Silmaril.Proofs.Games.AnsPull.pullAns_pair σ₁ σ₂

/-- **A relabelling handler below a pairing distributes over it.** -/
theorem ofHandler_ansH_comp_pair {F₁ F₂ : Sig.{u}} (σ₁ : DStrategy (Sig.mk E.Op B') F₁)
    (σ₂ : DStrategy (Sig.mk E.Op B') F₂) :
    (DStrategy.ofHandler (ansH k)).comp (σ₁.pair σ₂) =
      ((DStrategy.ofHandler (ansH k)).comp σ₁).pair ((DStrategy.ofHandler (ansH k)).comp σ₂) :=
  Silmaril.Proofs.Games.AnsPull.ofHandler_ansH_comp_pair σ₁ σ₂

/-- **A relabelling handler below a handler** composes as handlers. -/
theorem ofHandler_ansH_comp_ofHandler (h : Handler (Sig.mk E.Op B') G) :
    (DStrategy.ofHandler (ansH k)).comp (DStrategy.ofHandler h) =
      DStrategy.ofHandler ((ansH k).comp h) :=
  Silmaril.Proofs.Games.AnsPull.ofHandler_ansH_comp_ofHandler h

/-- **Relabelling and relabelling back is copycat.** -/
theorem ofHandler_ansH_comp_ansH {k' : (q : E.Op) → B' q → E.Ar q}
    (hk : ∀ q n, k' q (k q n) = n) :
    (DStrategy.ofHandler (ansH k)).comp
        (DStrategy.ofHandler (ansH (F := Sig.mk E.Op B') (B' := E.Ar) k')) =
      DStrategy.id E :=
  Silmaril.Proofs.Games.AnsPull.ofHandler_ansH_comp_ansH hk

/-- **Relabelling the hidden middle interface of a composite changes nothing.** -/
theorem comp_ansH_comp_ansH_comp {H : Sig.{u}} {k' : (q : E.Op) → B' q → E.Ar q}
    (hk : ∀ q n, k' q (k q n) = n) (σ : DStrategy F E) (τ : DStrategy E H) :
    (σ.comp (DStrategy.ofHandler (ansH k))).comp
        ((DStrategy.ofHandler (ansH (F := Sig.mk E.Op B') (B' := E.Ar) k')).comp τ) =
      σ.comp τ :=
  Silmaril.Proofs.Games.AnsPull.comp_ansH_comp_ansH_comp hk σ τ

end Below

section Above

variable {B : F.Op → Type u} {k : (q : F.Op) → F.Ar q → B q} {k' : (q : F.Op) → B q → F.Ar q}

/-- **An invertible relabelling is the pullback along its inverse.** -/
theorem mapAns_eq_pull (hk : ∀ q n, k' q (k q n) = n) (hk' : ∀ q n, k q (k' q n) = n)
    (σ : DStrategy E F) :
    σ.mapAns k = σ.pull (ansMove (F := Sig.mk F.Op B) k') posAns
      (pullData_ansMove (F := Sig.mk F.Op B) k') :=
  Silmaril.Proofs.Games.AnsPull.mapAns_eq_pull hk hk' σ

/-- **An invertible relabelling handler above a handler** composes as handlers. -/
theorem ofHandler_comp_ansH (hk : ∀ q n, k' q (k q n) = n) (hk' : ∀ q n, k q (k' q n) = n)
    (h : Handler E F) :
    (DStrategy.ofHandler h).comp (DStrategy.ofHandler (ansH k)) =
      DStrategy.ofHandler (h.comp (ansH k)) :=
  Silmaril.Proofs.Games.AnsPull.ofHandler_comp_ansH hk hk' h

end Above

/-- **Invertible relabellings above the components of a pairing** are the side-by-side
relabelling above the pairing. -/
theorem mapAns_pair {F₁ F₂ : Sig.{u}} {B₁ : F₁.Op → Type u} {B₂ : F₂.Op → Type u}
    {k₁ : (q : F₁.Op) → F₁.Ar q → B₁ q} {k₁' : (q : F₁.Op) → B₁ q → F₁.Ar q}
    {k₂ : (q : F₂.Op) → F₂.Ar q → B₂ q} {k₂' : (q : F₂.Op) → B₂ q → F₂.Ar q}
    (hk₁ : ∀ q n, k₁' q (k₁ q n) = n) (hk₁' : ∀ q n, k₁ q (k₁' q n) = n)
    (hk₂ : ∀ q n, k₂' q (k₂ q n) = n) (hk₂' : ∀ q n, k₂ q (k₂' q n) = n)
    (σ₁ : DStrategy E F₁) (σ₂ : DStrategy E F₂) :
    (σ₁.mapAns k₁).pair (σ₂.mapAns k₂) =
      (σ₁.pair σ₂).mapAns (sumAns (B₁ := B₁) (B₂ := B₂) k₁ k₂) :=
  Silmaril.Proofs.Games.AnsPull.mapAns_pair hk₁ hk₁' hk₂ hk₂' σ₁ σ₂

end DStrategy

end Silmaril.Games
