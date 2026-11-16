module

public import Silmaril.Games.Abstract.SessionPair.Defs
public import Silmaril.Games.Abstract.StratThread.Thms

/-!
# Pairing sessions: the paired triple

* Behaviours, call prefixes and streams of the paired triple are those of the component of the
  question (`mem_pairS_inl`, `satP_pairS_inl`, …).
* Coherence: no plain traps (`noPlainTrap_pairS`), store determinism (`storeDet_pairS`) and
  determinism given answers (`det_pairS`) are preserved.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionPair

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratThread
open Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.StratObs (callMoves satP CallPre)

universe u

variable {E : Sig.{u}} {S₁ S₂ A₁ A₂ B₁ B₂ : Type u}
  {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})} {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})}

theorem mem_pairS_inl {σ : S₁ × S₂} {a : A₁}
    {x : List (Call E) × End (S₁ × S₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1})} :
    x ∈ (pairS t₁ t₂).1 σ (.inl a) ↔ ∃ e, (x.1, e) ∈ t₁.1 σ.1 a ∧ x.2 = pairEndL σ.2 e := by
  constructor
  · rintro ⟨⟨c, e⟩, h, rfl⟩
    exact ⟨e, h, rfl⟩
  · rintro ⟨e, h, he⟩
    exact ⟨(x.1, e), h, Prod.ext rfl he.symm⟩

theorem mem_pairS_inr {σ : S₁ × S₂} {a : A₂}
    {x : List (Call E) × End (S₁ × S₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1})} :
    x ∈ (pairS t₁ t₂).1 σ (.inr a) ↔ ∃ e, (x.1, e) ∈ t₂.1 σ.2 a ∧ x.2 = pairEndR σ.1 e := by
  constructor
  · rintro ⟨⟨c, e⟩, h, rfl⟩
    exact ⟨e, h, rfl⟩
  · rintro ⟨e, h, he⟩
    exact ⟨(x.1, e), h, Prod.ext rfl he.symm⟩

theorem satP_pairS_inl (σ : S₁ × S₂) (a : A₁) :
    satP (pairS t₁ t₂) σ (.inl a) = satP t₁ σ.1 a := by
  ext ⟨c, m⟩
  simp only [satP, Set.mem_ofPred_eq]
  refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr ?_ Iff.rfl))
  constructor
  · rintro ⟨d, e, h, hc⟩
    obtain ⟨e', h', -⟩ := mem_pairS_inl.1 h
    exact ⟨d, e', h', hc⟩
  · rintro ⟨d, e, h, hc⟩
    exact ⟨d, pairEndL σ.2 e, mem_pairS_inl.2 ⟨e, h, rfl⟩, hc⟩

theorem satP_pairS_inr (σ : S₁ × S₂) (a : A₂) :
    satP (pairS t₁ t₂) σ (.inr a) = satP t₂ σ.2 a := by
  ext ⟨c, m⟩
  simp only [satP, Set.mem_ofPred_eq]
  refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr ?_ Iff.rfl))
  constructor
  · rintro ⟨d, e, h, hc⟩
    obtain ⟨e', h', -⟩ := mem_pairS_inr.1 h
    exact ⟨d, e', h', hc⟩
  · rintro ⟨d, e, h, hc⟩
    exact ⟨d, pairEndR σ.1 e, mem_pairS_inr.2 ⟨e, h, rfl⟩, hc⟩

/-! ## Coherence -/

theorem noPlainTrap_pairS (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂) :
    NoPlainTrap (pairS t₁ t₂) := by
  rintro σ (a | a) c h
  · obtain ⟨e, he, hx⟩ := mem_pairS_inl.1 h
    cases e with
    | trap => exact h₁ _ _ _ he
    | ret => simp [pairEndL] at hx
    | div => simp [pairEndL] at hx
  · obtain ⟨e, he, hx⟩ := mem_pairS_inr.1 h
    cases e with
    | trap => exact h₂ _ _ _ he
    | ret => simp [pairEndR] at hx
    | div => simp [pairEndR] at hx

theorem storeDet_pairS (h₁ : StoreDet t₁) (h₂ : StoreDet t₂) : StoreDet (pairS t₁ t₂) := by
  rintro σ (a | a) c b τ₁ τ₂ hτ₁ hτ₂
  · obtain ⟨e₁, he₁, hx₁⟩ := mem_pairS_inl.1 hτ₁
    obtain ⟨e₂, he₂, hx₂⟩ := mem_pairS_inl.1 hτ₂
    cases e₁ <;> cases e₂ <;> simp only [pairEndL, End.ret.injEq, reduceCtorEq] at hx₁ hx₂
    obtain ⟨rfl, rfl⟩ := hx₁
    obtain ⟨hb, rfl⟩ := hx₂
    cases Sum.map_injective.2 ⟨Sum.inl_injective, Function.injective_id⟩ hb
    rw [h₁ _ _ _ _ _ _ he₁ he₂]
  · obtain ⟨e₁, he₁, hx₁⟩ := mem_pairS_inr.1 hτ₁
    obtain ⟨e₂, he₂, hx₂⟩ := mem_pairS_inr.1 hτ₂
    cases e₁ <;> cases e₂ <;> simp only [pairEndR, End.ret.injEq, reduceCtorEq] at hx₁ hx₂
    obtain ⟨rfl, rfl⟩ := hx₁
    obtain ⟨hb, rfl⟩ := hx₂
    cases Sum.map_injective.2 ⟨Sum.inr_injective, Function.injective_id⟩ hb
    rw [h₂ _ _ _ _ _ _ he₁ he₂]

theorem agree_map {S S' B B' : Type u} (g : End S B → End S' B') {c₁ c₂ : List (Call E)}
    {e₁ e₂ : End S B} (h : AFun.Agree c₁ e₁ c₂ e₂) : AFun.Agree c₁ (g e₁) c₂ (g e₂) := by
  induction c₁ generalizing c₂ with
  | nil =>
    rcases c₂ with _ | ⟨⟨m, n⟩, c₂⟩
    · exact congrArg g h
    · exact h.elim
  | cons x c₁ ih =>
    rcases c₂ with _ | ⟨⟨m, n⟩, c₂⟩
    · exact h.elim
    · obtain ⟨m₁, n₁⟩ := x
      exact ⟨h.1, fun hn => ih (h.2 hn)⟩

theorem det_pairS (h₁ : AFun.Det t₁.1) (h₂ : AFun.Det t₂.1) : AFun.Det (pairS t₁ t₂).1 := by
  rintro σ (a | a) x y hx hy
  · obtain ⟨e₁, he₁, rx⟩ := mem_pairS_inl.1 hx
    obtain ⟨e₂, he₂, ry⟩ := mem_pairS_inl.1 hy
    rw [rx, ry]
    exact agree_map (pairEndL σ.2) (h₁ _ _ _ _ he₁ he₂)
  · obtain ⟨e₁, he₁, rx⟩ := mem_pairS_inr.1 hx
    obtain ⟨e₂, he₂, ry⟩ := mem_pairS_inr.1 hy
    rw [rx, ry]
    exact agree_map (pairEndR σ.1) (h₂ _ _ _ _ he₁ he₂)

end Silmaril.Proofs.Games.Abstract.SessionPair
