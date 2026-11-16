module

public import Silmaril.Proofs.Games.Abstract.SessionLinkDead.Thread
public import Silmaril.Games.Abstract.StratSession.Thms

/-!
# The dead server without plain traps

Without plain traps the dead server never dies: from `some s` its rounds and coherent services
stay at live stores and are those of `t` (`rounds_deadS_iff`, `infServe_deadS_iff`). So `linkSD t u`
at `(some s, s')` is `linkS t u` at `(s, s')`, the final stores embedded (`linkSD_some`), and the
embedding is a bisimulation of the linked triples (`threadS_linkSD`).
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkDead

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionLinkDead

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

theorem ret_deadS_iff (hnt : NoPlainTrap t) {s : S} {a : A} {c : List (Call E)}
    {b : B ⊕ PUnit.{u + 1}} {σ : Option S} :
    (c, End.ret b σ) ∈ (deadS t).1 (some s) a ↔
      ∃ s₁, σ = some s₁ ∧ (c, End.ret b s₁) ∈ t.1 s a := by
  constructor
  · rintro (⟨y, s₁, h, he⟩ | ⟨h, -, -⟩ | ⟨_, he⟩)
    · simp only [End.ret.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨s₁, rfl, h⟩
    · exact (hnt _ _ _ h).elim
    · cases he
  · rintro ⟨s₁, rfl, h⟩
    exact .inl ⟨b, s₁, h, rfl⟩

theorem div_deadS_iff {σ : Option S} {a : A} {c : List (Call E)} :
    (c, End.div) ∈ (deadS t).1 σ a ↔ ∃ s, σ = some s ∧ (c, End.div) ∈ t.1 s a := by
  constructor
  · rcases σ with _ | s
    · intro h; exact h.elim
    · rintro (⟨_, _, _, he⟩ | ⟨_, _, he⟩ | ⟨h, -⟩)
      · cases he
      · cases he
      · exact ⟨s, rfl, h⟩
  · rintro ⟨s, rfl, h⟩
    exact .inr (.inr ⟨h, rfl⟩)

theorem rounds_deadS_iff (hnt : NoPlainTrap t) {s : S} {σ : Option S}
    {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} :
    Rounds (deadS t) (some s) rs σ ↔ ∃ s₁, σ = some s₁ ∧ Rounds t s rs s₁ := by
  constructor
  · intro h
    induction rs generalizing s with
    | nil => cases h; exact ⟨s, rfl, .nil _⟩
    | cons x rs ih =>
      cases h with
      | cons hb hr =>
        obtain ⟨s₂, rfl, hb'⟩ := (ret_deadS_iff hnt).1 hb
        obtain ⟨s₁, rfl, hr'⟩ := ih hr
        exact ⟨s₁, rfl, .cons hb' hr'⟩
  · rintro ⟨s₁, rfl, h⟩
    exact rounds_deadS h

theorem infServe_deadS_iff (hnt : NoPlainTrap t) {s : S} {ω : ℕ → Call (sig1 A B)}
    {l : ℕ → List (Call E)} {st : ℕ → Option S} :
    InfServe (deadS t) (some s) ω l st ↔
      ∃ st', InfServe t s ω l st' ∧ ∀ k, st k = some (st' k) := by
  constructor
  · intro h
    have hl : ∀ k, ∃ x, st k = some x := by
      intro k
      induction k with
      | zero => exact ⟨s, h.zero⟩
      | succ k ih =>
        obtain ⟨x, hx⟩ := ih
        have := h.step k
        rw [hx] at this
        obtain ⟨s₁, h₁, -⟩ := (ret_deadS_iff hnt).1 this
        exact ⟨s₁, h₁⟩
    have he : ∀ k, st k = some ((st k).getD s) := fun k => by
      obtain ⟨x, hx⟩ := hl k
      rw [hx]; rfl
    refine ⟨fun k => (st k).getD s, ⟨?_, fun k => ?_⟩, he⟩
    · have := h.zero
      rw [he 0] at this
      exact Option.some.inj this
    · have := h.step k
      rw [he k, he (k + 1)] at this
      obtain ⟨_, h₁, h₂⟩ := (ret_deadS_iff hnt).1 this
      cases h₁
      exact h₂
  · rintro ⟨st', h, he⟩
    refine ⟨by rw [he, h.zero], fun k => ?_⟩
    rw [he, he]
    exact .inl ⟨_, _, h.step k, rfl⟩

theorem someEnd_linkEnd {s₁ : S} {e : End S' (B' ⊕ PUnit.{u + 1})} :
    someEnd (linkEnd s₁ e) = linkEnd (some s₁) e := by
  cases e <;> rfl

theorem linkSD_some_fst (hnt : NoPlainTrap t) (s : S) (s' : S') (a' : A') :
    (linkSD t u).1 (some s, s') a' = (fun x => (x.1, someEnd x.2)) '' (linkS t u).1 (s, s') a' := by
  ext x
  constructor
  · rintro (⟨rs, σ₁, e, hr, he, rfl⟩ | ⟨rs, σ₁, a, c, hr, hp, hd, rfl⟩ |
      ⟨ω, hω, l, st, n, hi, hl, rfl⟩)
    · obtain ⟨s₁, rfl, hr'⟩ := (rounds_deadS_iff hnt).1 hr
      exact ⟨_, .inl ⟨rs, s₁, e, hr', he, rfl⟩, by simp [someEnd_linkEnd]⟩
    · obtain ⟨s₁, rfl, hr'⟩ := (rounds_deadS_iff hnt).1 hr
      obtain ⟨_, h, hd⟩ := div_deadS_iff.1 hd
      cases h
      exact ⟨_, .inr (.inl ⟨rs, _, a, c, hr', hp, hd, rfl⟩), rfl⟩
    · obtain ⟨st', hi, -⟩ := (infServe_deadS_iff hnt).1 hi
      exact ⟨_, .inr (.inr ⟨ω, hω, l, st', n, hi, hl, rfl⟩), rfl⟩
  · rintro ⟨_, (⟨rs, s₁, e, hr, he, rfl⟩ | ⟨rs, s₁, a, c, hr, hp, hd, rfl⟩ |
      ⟨ω, hω, l, st, n, hi, hl, rfl⟩), rfl⟩
    · exact .inl ⟨rs, some s₁, e, rounds_deadS hr, he, by simp [someEnd_linkEnd]⟩
    · exact .inr (.inl ⟨rs, some s₁, a, c, rounds_deadS hr, hp, div_deadS_iff.2 ⟨_, rfl, hd⟩, rfl⟩)
    · exact .inr (.inr ⟨ω, hω, l, fun k => some (st k), n,
        (infServe_deadS_iff hnt).2 ⟨st, hi, fun _ => rfl⟩, hl, rfl⟩)

theorem linkSD_some_pend (hnt : NoPlainTrap t) (s : S) (s' : S') :
    (linkSD t u).2.1 (some s, s') = (linkS t u).2.1 (s, s') := by
  funext a'
  ext x
  constructor
  · rintro ⟨rs, σ₁, a, c, hr, hp, hc, hx⟩
    obtain ⟨s₁, rfl, hr'⟩ := (rounds_deadS_iff hnt).1 hr
    rw [satP_deadS_some] at hc
    exact ⟨rs, s₁, a, c, hr', hp, hc, hx⟩
  · rintro ⟨rs, s₁, a, c, hr, hp, hc, hx⟩
    refine ⟨rs, some s₁, a, c, rounds_deadS hr, hp, ?_, hx⟩
    rw [satP_deadS_some]; exact hc

theorem linkSD_some_inf (hnt : NoPlainTrap t) (s : S) (s' : S') :
    (linkSD t u).2.2 (some s, s') = (linkS t u).2.2 (s, s') := by
  funext a'
  ext ω
  constructor
  · rintro (⟨rs, σ₁, a, ω', hr, hp, hω, hk⟩ | ⟨ω', hω, l, st, hi, hu, hk⟩)
    · obtain ⟨s₁, rfl, hr'⟩ := (rounds_deadS_iff hnt).1 hr
      exact .inl ⟨rs, s₁, a, ω', hr', hp, hω, hk⟩
    · obtain ⟨st', hi, -⟩ := (infServe_deadS_iff hnt).1 hi
      exact .inr ⟨ω', hω, l, st', hi, hu, hk⟩
  · rintro (⟨rs, s₁, a, ω', hr, hp, hω, hk⟩ | ⟨ω', hω, l, st, hi, hu, hk⟩)
    · exact .inl ⟨rs, some s₁, a, ω', rounds_deadS hr, hp, hω, hk⟩
    · exact .inr ⟨ω', hω, l, fun k => some (st k),
        (infServe_deadS_iff hnt).2 ⟨st, hi, fun _ => rfl⟩, hu, hk⟩

/-! ## The embedding is a bisimulation -/

theorem isBisim_some (hnt : NoPlainTrap t) :
    IsBisim (linkSD t u) (linkS t u) fun σ τ => σ = (some τ.1, τ.2) := by
  rintro _ ⟨s, s'⟩ rfl
  have h₁ := linkSD_some_fst (u := u) hnt s s'
  have hlog : ∀ a' d, (∃ e, (d, e) ∈ (linkSD t u).1 (some s, s') a') ↔
      ∃ e, (d, e) ∈ (linkS t u).1 (s, s') a' := fun a' d => by
    rw [h₁]
    exact ⟨fun ⟨_, ⟨y, hy, he⟩⟩ => ⟨y.2, by cases he; exact hy⟩,
      fun ⟨e, he⟩ => ⟨_, ⟨_, he, rfl⟩⟩⟩
  refine ⟨fun a c => ?_, fun a c => ?_, ?_, linkSD_some_inf hnt s s', fun a c b σ₁ h => ?_,
    fun a c b τ₁ h => ?_⟩
  · rw [h₁]
    constructor
    · rintro ⟨⟨_, e⟩, hy, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, he⟩ := he
      cases e <;> simp [someEnd] at he
      exact hy
    · intro h; exact ⟨_, h, rfl⟩
  · rw [h₁]
    constructor
    · rintro ⟨⟨_, e⟩, hy, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, he⟩ := he
      cases e <;> simp [someEnd] at he
      exact hy
    · intro h; exact ⟨_, h, rfl⟩
  · funext a'
    ext x
    have hp := congrFun (linkSD_some_pend (u := u) hnt s s') a'
    have hi := congrFun (linkSD_some_inf (u := u) hnt s s') a'
    simp only [satP, hp, hi, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h | ⟨d, e, he, hc⟩ | h)
      · exact .inl h
      · exact .inr (.inl h)
      · obtain ⟨e', he'⟩ := (hlog a' d).1 ⟨e, he⟩
        exact .inr (.inr (.inl ⟨d, e', he', hc⟩))
      · exact .inr (.inr (.inr h))
    · rintro (h | h | ⟨d, e, he, hc⟩ | h)
      · exact .inl h
      · exact .inr (.inl h)
      · obtain ⟨e', he'⟩ := (hlog a' d).2 ⟨e, he⟩
        exact .inr (.inr (.inl ⟨d, e', he', hc⟩))
      · exact .inr (.inr (.inr h))
  · rw [h₁] at h
    obtain ⟨⟨_, e⟩, hy, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    cases e with
    | ret b' τ₁ =>
      simp only [someEnd, End.ret.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨τ₁, hy, rfl⟩
    | trap => cases he
    | div => cases he
  · exact ⟨_, by rw [h₁]; exact ⟨_, h, rfl⟩, rfl⟩

theorem threadS_linkSD (hnt : NoPlainTrap t) (s₀ : S) (s₀' : S') :
    threadS (linkSD t u) (some s₀, s₀') = threadS (linkS t u) (s₀, s₀') :=
  threadS_eq_of_obsEq ⟨_, isBisim_some hnt, rfl⟩

end Silmaril.Proofs.Games.Abstract.SessionLinkDead
