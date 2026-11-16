module

public import Silmaril.Games.Abstract.SessionPair.Defs
public import Silmaril.Games.Abstract.StratThread.Thms
public import Silmaril.Games.DPair.Defs
public import Silmaril.Proofs.Games.Abstract.SessionPair.Sim
import Silmaril.Proofs.Games.Abstract.SessionPair.Basic

/-!
# Pairing sessions: finite plays and divergence

For triples without plain traps, a play `q` of the pairing of two sessions is a play iff its
relabelling `q.map pairMove` is a play of the paired session (`mem_pair_iff`), and the same for
divergent plays (`mem_div_pair_iff`). Every play of the paired session is a relabelled play
(`exists_map_pairMove`).
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionPair

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratThread
open Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.StratObs (callMoves satP)

universe u

variable {E : Sig.{u}} {S₁ S₂ A₁ A₂ B₁ B₂ : Type u}
  {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})} {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})}
  {s₁ : S₁} {s₂ : S₂}

theorem pairMove_injective :
    Function.Injective (pairMove (E := E) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)) := by
  rintro (e | (a | ⟨a | a, x⟩)) (e' | (a' | ⟨a' | a', x'⟩)) h <;> simp_all [pairMove]
  · injection h
  · obtain ⟨rfl, hx⟩ := h
    rw [Sum.map_injective.2 ⟨Sum.inl_injective, Function.injective_id⟩ hx]
  · obtain ⟨rfl, hx⟩ := h
    rw [Sum.map_injective.2 ⟨Sum.inr_injective, Function.injective_id⟩ hx]

theorem map_pm (q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))) :
    (q.map pairMove).map unmerge = q.map pm := by
  simp [List.map_map, Function.comp_def]

/-- A run of the paired automaton is a path of the pairing game. -/
theorem path_of_run {q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} :
    ∀ {x y : TSt E (S₁ × S₂) (A₁ ⊕ A₂)},
      TRun (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) x (q.map pm) y → Path (posOf x) q (posOf y) := by
  induction q with
  | nil => intro x y h; cases h; exact .nil _
  | cons o q ih =>
    intro x y h
    cases h with
    | cons hs hq => exact .cons (pos_step hs) (ih hq)

theorem mem_pair_iff (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂)
    {q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} :
    q ∈ ((threadS t₁ s₁).pair (threadS t₂ s₂)).toStrategy ↔
      q.map pairMove ∈ (threadS (pairS t₁ t₂) (s₁, s₂)).toStrategy := by
  rw [mem_threadS_iff (noPlainTrap_pairS h₁ h₂), map_pm]
  constructor
  · rintro ⟨⟨g, hl⟩, hq₁, hq₂⟩
    obtain ⟨y₁, r₁⟩ := (mem_threadS_iff h₁).1 hq₁
    obtain ⟨y₂, r₂⟩ := (mem_threadS_iff h₂).1 hq₂
    obtain ⟨y, hy, -⟩ := bwd r₁ r₂ (.idle s₁ s₂ false) hl
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y₁, y₂, r₁, r₂, -⟩ := fwd hy (.idle s₁ s₂ false)
    exact ⟨⟨_, path_of_run hy⟩, (mem_threadS_iff h₁).2 ⟨y₁, r₁⟩, (mem_threadS_iff h₂).2 ⟨y₂, r₂⟩⟩

/-- Every move of the paired automaton is a relabelled move. -/
theorem exists_pairMove_of_step {x y : TSt E (S₁ × S₂) (A₁ ⊕ A₂)}
    {o : Move E (sig1 (A₁ ⊕ A₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1}))}
    (h : TStep (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) x o y) : ∃ o', pairMove o' = relMove o := by
  cases h with
  | ask s a => exact ⟨.inr (.ask a), rfl⟩
  | call s a c m => exact ⟨.inl (.ask m), rfl⟩
  | reply s a c m n => exact ⟨.inl (.ans m n), rfl⟩
  | deadAsk a => exact ⟨.inr (.ask a), rfl⟩
  | trap s a c =>
    rcases a with a | a
    · exact ⟨.inr (.ans (.inl a) (.inr PUnit.unit)), rfl⟩
    · exact ⟨.inr (.ans (.inr a) (.inr PUnit.unit)), rfl⟩
  | ret s a c b s' hb =>
    rcases a with a | a
    · obtain ⟨e, -, he⟩ := mem_pairS_inl.1 hb
      cases e with
      | ret x _ =>
        simp only [endL, End.ret.injEq] at he
        exact ⟨.inr (.ans (.inl a) x), by rw [he.1]; rfl⟩
      | trap => simp [endL] at he
      | div => simp [endL] at he
    · obtain ⟨e, -, he⟩ := mem_pairS_inr.1 hb
      cases e with
      | ret x _ =>
        simp only [endR, End.ret.injEq] at he
        exact ⟨.inr (.ans (.inr a) x), by rw [he.1]; rfl⟩
      | trap => simp [endR] at he
      | div => simp [endR] at he

theorem exists_map_of_run {x y : TSt E (S₁ × S₂) (A₁ ⊕ A₂)}
    {p : List (Move E (sig1 (A₁ ⊕ A₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1})))}
    (h : TRun (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) x p y) :
    ∃ q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)), q.map pairMove = p.map relMove := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | cons hs _ ih =>
    obtain ⟨o', ho⟩ := exists_pairMove_of_step hs
    obtain ⟨q, hq⟩ := ih
    exact ⟨o' :: q, by simp [ho, hq]⟩

/-- Every play of the paired session is a relabelled play. -/
theorem exists_map_pairMove {p : List (Move E (sig1 (A₁ ⊕ A₂) (B₁ ⊕ B₂)))}
    (hp : p ∈ (threadS (pairS t₁ t₂) (s₁, s₂)).toStrategy) :
    ∃ q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)), q.map pairMove = p := by
  obtain ⟨p', ⟨_, hp'⟩, rfl⟩ := hp
  exact exists_map_of_run hp'

theorem mem_div_pair_iff (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂)
    {q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} :
    q ∈ ((threadS t₁ s₁).pair (threadS t₂ s₂)).div ↔
      q.map pairMove ∈ (threadS (pairS t₁ t₂) (s₁, s₂)).div := by
  rw [mem_div_threadS_iff (noPlainTrap_pairS h₁ h₂), map_pm]
  constructor
  · rintro ⟨⟨⟨g, hl⟩, hq₁, hq₂⟩, hd | hd⟩
    · obtain ⟨s, a, c, r₁, hd⟩ := (mem_div_threadS_iff h₁).1 hd
      obtain ⟨y₂, r₂⟩ := (mem_threadS_iff h₂).1 hq₂
      obtain ⟨y, hy, hr⟩ := bwd r₁ r₂ (.idle s₁ s₂ false) hl
      generalize Split.side false q = b at hr
      cases hr with
      | runL _ s₂' =>
        exact ⟨(s, s₂'), .inl a, c, hy, mem_pairS_inl.2 ⟨.div, hd, rfl⟩⟩
    · obtain ⟨s, a, c, r₂, hd⟩ := (mem_div_threadS_iff h₂).1 hd
      obtain ⟨y₁, r₁⟩ := (mem_threadS_iff h₁).1 hq₁
      obtain ⟨y, hy, hr⟩ := bwd r₁ r₂ (.idle s₁ s₂ false) hl
      generalize Split.side false q = b at hr
      cases hr with
      | runR s₁' _ =>
        exact ⟨(s₁', s), .inr a, c, hy, mem_pairS_inr.2 ⟨.div, hd, rfl⟩⟩
  · rintro ⟨σ, a, c, hy, hd⟩
    obtain ⟨y₁, y₂, r₁, r₂, hr⟩ := fwd hy (.idle s₁ s₂ false)
    refine ⟨⟨⟨_, path_of_run hy⟩, (mem_threadS_iff h₁).2 ⟨y₁, r₁⟩,
      (mem_threadS_iff h₂).2 ⟨y₂, r₂⟩⟩, ?_⟩
    generalize Split.side false q = b at hr
    cases hr with
    | runL s s' a c =>
      obtain ⟨e, he, hx⟩ := mem_pairS_inl.1 hd
      cases e with
      | div => exact .inl ((mem_div_threadS_iff h₁).2 ⟨_, _, _, r₁, he⟩)
      | ret => simp [endL] at hx
      | trap => simp [endL] at hx
    | runR s s' a c =>
      obtain ⟨e, he, hx⟩ := mem_pairS_inr.1 hd
      cases e with
      | div => exact .inr ((mem_div_threadS_iff h₂).2 ⟨_, _, _, r₂, he⟩)
      | ret => simp [endR] at hx
      | trap => simp [endR] at hx

end Silmaril.Proofs.Games.Abstract.SessionPair
