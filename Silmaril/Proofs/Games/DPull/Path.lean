module

public import Silmaril.Games.Div.Defs

/-!
# Pulling plays back along a move map: paths (proofs)

A move map `f : Move E F → Move E' F'` with a position map `pf` that sends steps to steps
(`hs`) and lets every step of an image position along an image move be lifted (`hl`)
transports paths both ways: forwards (`path_map`) and, from an image position, backwards
(`path_lift`). With `pf .idle = .idle` a play whose image is legal is legal (`legal_lift`), and
when `pf` reflects running positions a play whose image ends running ends running
(`run_lift`) and Opponent moves go to Opponent moves (`isO_map`). Images of infinite traces are
infinite traces (`isInfPlay_image`). Used by `Silmaril.Games.DPull.Defs`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.DPull

open Silmaril.Games

universe u

variable {E F E' F' : Sig.{u}} {f : Move E F → Move E' F'} {pf : Pos E F → Pos E' F'}

theorem path_map (hs : ∀ {x o y}, Step x o y → Step (pf x) (f o) (pf y))
    {x y : Pos E F} {p : List (Move E F)} (h : Path x p y) : Path (pf x) (p.map f) (pf y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (hs h) ih

theorem path_lift (hs : ∀ {x o y}, Step x o y → Step (pf x) (f o) (pf y))
    (hl : ∀ {x o y'}, Step (pf x) (f o) y' → ∃ y, Step x o y)
    {x : Pos E F} {p : List (Move E F)} {y' : Pos E' F'} (h : Path (pf x) (p.map f) y') :
    ∃ y, Path x p y ∧ pf y = y' := by
  induction p generalizing x with
  | nil =>
    cases h
    exact ⟨x, .nil _, rfl⟩
  | cons o p ih =>
    cases h with
    | cons hs' hp =>
      obtain ⟨z, hz⟩ := hl hs'
      cases Step.det hs' (hs hz)
      obtain ⟨y, hy, rfl⟩ := ih hp
      exact ⟨y, .cons hz hy, rfl⟩

theorem legal_lift (hs : ∀ {x o y}, Step x o y → Step (pf x) (f o) (pf y))
    (hl : ∀ {x o y'}, Step (pf x) (f o) y' → ∃ y, Step x o y) (hi : pf .idle = .idle)
    {p : List (Move E F)} (h : Legal (p.map f)) : Legal p := by
  obtain ⟨y', hy'⟩ := h
  rw [← hi] at hy'
  obtain ⟨y, hy, -⟩ := path_lift hs hl hy'
  exact ⟨y, hy⟩

theorem run_lift (hs : ∀ {x o y}, Step x o y → Step (pf x) (f o) (pf y))
    (hl : ∀ {x o y'}, Step (pf x) (f o) y' → ∃ y, Step x o y) (hi : pf .idle = .idle)
    (hr : ∀ {x q'}, pf x = .run q' → ∃ q, x = .run q)
    {p : List (Move E F)} (h : ∃ q', Path .idle (p.map f) (Pos.run q')) :
    ∃ q, Path .idle p (Pos.run q) := by
  obtain ⟨q', hq'⟩ := h
  rw [← hi] at hq'
  obtain ⟨y, hy, he⟩ := path_lift hs hl hq'
  obtain ⟨q, rfl⟩ := hr he
  exact ⟨q, hy⟩

/-- A Proponent step starts from a running position. -/
theorem run_of_isP {x y : Pos E' F'} {o : Move E' F'} (h : Step x o y) (ho : o.IsP) :
    ∃ q, x = .run q := by
  cases h <;> simp_all [Move.IsP]

theorem isO_map (hs : ∀ {x o y}, Step x o y → Step (pf x) (f o) (pf y))
    (hr : ∀ {x q'}, pf x = .run q' → ∃ q, x = .run q)
    {x y : Pos E F} {o : Move E F} (h : Step x o y) (ho : o.IsO) : (f o).IsO := by
  rcases (hs h).isO_or_isP with h' | h'
  · exact h'
  · obtain ⟨q', hq'⟩ := run_of_isP (hs h) h'
    obtain ⟨q, rfl⟩ := hr hq'
    cases h <;> simp_all [Move.IsO]

theorem isInfPlay_image {α β : Type u} (g : α → β) {I : Set (List α)} (hI : IsInfPlay I) :
    IsInfPlay (List.map g '' I) where
  of_prefix := by
    rintro s _ ⟨t, ht, rfl⟩ hs
    refine ⟨t.take s.length, hI.of_prefix ht (List.take_prefix _ _), ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hs).symm
  total := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    rcases hI.total hs ht with h | h
    · exact .inl (h.map _)
    · exact .inr (h.map _)
  unbounded k := by
    obtain ⟨s, hs, hk⟩ := hI.unbounded k
    exact ⟨_, ⟨s, hs, rfl⟩, by simpa using hk⟩

end Silmaril.Proofs.Games.DPull
