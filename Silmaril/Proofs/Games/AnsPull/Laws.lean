module

public import Silmaril.Proofs.Games.AnsPull.Comp
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Games.AnsMap.Thms

/-!
# Handler laws for relabelling handlers (proofs)

From `ofHandler_ansH_comp` (below) and `DStrategy.comp_ansH` (above):

* `ofHandler_ansH_comp_pair`: a relabelling handler below a pairing is duplicated (`pull_pair`
  with `halves_lowMove`);
* `mapAns_pair`: invertible relabellings above the components of a pairing are the side-by-side
  relabelling above the pairing (`mapAns_eq_pull`, `pull_pair` with `halves_sumMove`);
* `ofHandler_ansH_comp_ofHandler`, `ofHandler_comp_ansH`: a relabelling handler below any handler,
  or an invertible one above it, composes as handlers. Both sides are divergence-free and have
  every limit of their plays (`pull_limits`, `SessionRoute.ofHandler_eq_limits`), and their
  finite plays agree (`Strategy.ofHandler_comp`);
* `ofHandler_ansH_comp_ansH`: relabelling along `k` then back along a left inverse is copycat;
  hence `comp_ansH_comp_ansH_comp`: relabelling the hidden middle interface of a composite changes
  nothing.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.AnsPull

open Silmaril.Games Silmaril.Games.Abstract.SessionRoute

universe u

variable {E F G : Sig.{u}}

section Below

variable {B' : E.Op → Type u} {k : (q : E.Op) → E.Ar q → B' q}

theorem pullAns_pair {F₁ F₂ : Sig.{u}} (σ₁ : DStrategy (Sig.mk E.Op B') F₁)
    (σ₂ : DStrategy (Sig.mk E.Op B') F₂) :
    (σ₁.pair σ₂).pullAns k = (σ₁.pullAns k).pair (σ₂.pullAns k) :=
  pull_pair (pullData_lowMove k) (pullData_lowMove k) (pullData_lowMove k)
    (halves_lowMove k false) σ₁ σ₂

theorem ofHandler_ansH_comp_pair {F₁ F₂ : Sig.{u}} (σ₁ : DStrategy (Sig.mk E.Op B') F₁)
    (σ₂ : DStrategy (Sig.mk E.Op B') F₂) :
    (DStrategy.ofHandler (ansH k)).comp (σ₁.pair σ₂) =
      ((DStrategy.ofHandler (ansH k)).comp σ₁).pair ((DStrategy.ofHandler (ansH k)).comp σ₂) := by
  rw [ofHandler_ansH_comp, ofHandler_ansH_comp, ofHandler_ansH_comp, pullAns_pair]

theorem ofHandler_ansH_comp_ofHandler (h : Handler (Sig.mk E.Op B') G) :
    (DStrategy.ofHandler (ansH k)).comp (DStrategy.ofHandler h) =
      DStrategy.ofHandler ((ansH k).comp h) := by
  have e : (DStrategy.ofHandler (ansH k)).comp (DStrategy.ofHandler h) =
      DStrategy.limits ((Strategy.ofHandler h).pull (lowMove k) posLow (pullData_lowMove k)) := by
    rw [ofHandler_ansH_comp, DStrategy.pullAns, ofHandler_eq_limits h]
    exact pull_limits _ _
  rw [e, ofHandler_eq_limits ((ansH k).comp h), Strategy.ofHandler_comp]
  exact congrArg DStrategy.limits (congrArg DStrategy.toStrategy e).symm

theorem ofHandler_ansH_comp_ansH {k' : (q : E.Op) → B' q → E.Ar q}
    (hk : ∀ q n, k' q (k q n) = n) :
    (DStrategy.ofHandler (ansH k)).comp
        (DStrategy.ofHandler (ansH (F := Sig.mk E.Op B') (B' := E.Ar) k')) =
      DStrategy.id E := by
  have hh : (ansH k).comp (ansH (F := Sig.mk E.Op B') (B' := E.Ar) k') = Handler.id E := by
    funext q
    simp only [Handler.comp, ansH, Prog.interp, Prog.bind, Handler.id, Prog.lift, hk]
  rw [ofHandler_ansH_comp_ofHandler, hh, ofHandler_eq_limits, Strategy.ofHandler_id]
  rfl

theorem comp_ansH_comp_ansH_comp {H : Sig.{u}} {k' : (q : E.Op) → B' q → E.Ar q}
    (hk : ∀ q n, k' q (k q n) = n) (σ : DStrategy F E) (τ : DStrategy E H) :
    (σ.comp (DStrategy.ofHandler (ansH k))).comp
        ((DStrategy.ofHandler (ansH (F := Sig.mk E.Op B') (B' := E.Ar) k')).comp τ) =
      σ.comp τ := by
  rw [DStrategy.comp_assoc, ← DStrategy.comp_assoc (DStrategy.ofHandler (ansH k)),
    ofHandler_ansH_comp_ansH hk, DStrategy.id_comp]

end Below

section Above

variable {B : F.Op → Type u} {k : (q : F.Op) → F.Ar q → B q} {k' : (q : F.Op) → B q → F.Ar q}

theorem ofHandler_comp_ansH (hk : ∀ q n, k' q (k q n) = n) (hk' : ∀ q n, k q (k' q n) = n)
    (h : Handler E F) :
    (DStrategy.ofHandler h).comp (DStrategy.ofHandler (ansH k)) =
      DStrategy.ofHandler (h.comp (ansH k)) := by
  have e : (DStrategy.ofHandler h).comp (DStrategy.ofHandler (ansH k)) =
      DStrategy.limits ((Strategy.ofHandler h).pull (ansMove (F := Sig.mk F.Op B) k') posAns
        (pullData_ansMove (F := Sig.mk F.Op B) k')) := by
    rw [DStrategy.comp_ansH, mapAns_eq_pull hk hk', ofHandler_eq_limits h]
    exact pull_limits _ _
  rw [e, ofHandler_eq_limits (h.comp (ansH k)), Strategy.ofHandler_comp]
  exact congrArg DStrategy.limits (congrArg DStrategy.toStrategy e).symm

end Above

section Pair

variable {F₁ F₂ : Sig.{u}} {B₁ : F₁.Op → Type u} {B₂ : F₂.Op → Type u}
  {k₁ : (q : F₁.Op) → F₁.Ar q → B₁ q} {k₁' : (q : F₁.Op) → B₁ q → F₁.Ar q}
  {k₂ : (q : F₂.Op) → F₂.Ar q → B₂ q} {k₂' : (q : F₂.Op) → B₂ q → F₂.Ar q}

theorem mapAns_pair (hk₁ : ∀ q n, k₁' q (k₁ q n) = n) (hk₁' : ∀ q n, k₁ q (k₁' q n) = n)
    (hk₂ : ∀ q n, k₂' q (k₂ q n) = n) (hk₂' : ∀ q n, k₂ q (k₂' q n) = n)
    (σ₁ : DStrategy E F₁) (σ₂ : DStrategy E F₂) :
    (σ₁.mapAns k₁).pair (σ₂.mapAns k₂) =
      (σ₁.pair σ₂).mapAns (sumAns (B₁ := B₁) (B₂ := B₂) k₁ k₂) := by
  have hS := pullData_sumMove (E := E) (F₁ := Sig.mk F₁.Op B₁) (F₂ := Sig.mk F₂.Op B₂) k₁' k₂'
  have e : (σ₁.pair σ₂).mapAns (sumAns (B₁ := B₁) (B₂ := B₂) k₁ k₂) =
      (σ₁.pair σ₂).pull (sumMove (F₁ := Sig.mk F₁.Op B₁) (F₂ := Sig.mk F₂.Op B₂) k₁' k₂') posAns
        hS := by
    refine mapAns_eq_pull_of _ (fun o => ?_) (fun o => ?_) _
    · rcases o with _ | (_ | ⟨q | q, n⟩)
      · rfl
      · rfl
      · exact congrArg (fun r => (Sum.inr (Ev.ans (E := F₁ ⊕ₛ F₂) (Sum.inl q) r) :
          Move E (F₁ ⊕ₛ F₂))) (hk₁ q n)
      · exact congrArg (fun r => (Sum.inr (Ev.ans (E := F₁ ⊕ₛ F₂) (Sum.inr q) r) :
          Move E (F₁ ⊕ₛ F₂))) (hk₂ q n)
    · rcases o with _ | (_ | ⟨q | q, n⟩)
      · rfl
      · rfl
      · exact congrArg (fun r => (Sum.inr
          (Ev.ans (E := Sig.mk F₁.Op B₁ ⊕ₛ Sig.mk F₂.Op B₂) (Sum.inl q) r) :
            Move E (Sig.mk F₁.Op B₁ ⊕ₛ Sig.mk F₂.Op B₂))) (hk₁' q n)
      · exact congrArg (fun r => (Sum.inr
          (Ev.ans (E := Sig.mk F₁.Op B₁ ⊕ₛ Sig.mk F₂.Op B₂) (Sum.inr q) r) :
            Move E (Sig.mk F₁.Op B₁ ⊕ₛ Sig.mk F₂.Op B₂))) (hk₂' q n)
  rw [mapAns_eq_pull hk₁ hk₁', mapAns_eq_pull hk₂ hk₂', e]
  exact (pull_pair hS _ _ (halves_sumMove (E := E) (F₁ := Sig.mk F₁.Op B₁)
    (F₂ := Sig.mk F₂.Op B₂) k₁' k₂' false) σ₁ σ₂).symm

end Pair

end Silmaril.Proofs.Games.AnsPull
