module

public import Silmaril.Games.DPair.Defs
import Silmaril.Proofs.Games.DPair.Run

/-!
# Pairing divergence-observing strategies: proofs

* Lengths of halves (`halves_length`) and the projections of infinite plays
  (`isInfPlay_infL_iff`, `isInfPlay_infL_or_infR`).
* Lifting one side into the pairing (`halves_map_liftL`, `legal_map_liftL`,
  and the infinite plays `inf_map_liftL`).
-/

public section

namespace Silmaril.Proofs.Games.DPair

open Silmaril.Games Silmaril.Games.Split

universe u

variable {E F₁ F₂ : Sig.{u}}

/-! ## Projections of infinite plays -/

/-- A play is as long as its two halves together. -/
theorem halves_length (b : Bool) (p : List (Move E (F₁ ⊕ₛ F₂))) :
    (halves b p).1.length + (halves b p).2.length = p.length := by
  induction p generalizing b with
  | nil => rfl
  | cons x p ih =>
    have h₁ := ih false
    have h₂ := ih true
    have h₃ := ih b
    rcases x with e | (q | ⟨q, r⟩)
    · cases b <;> simp [halves] <;> omega
    · rcases q with q | q <;> simp [halves] <;> omega
    · rcases q with q | q <;> simp [halves] <;> omega

theorem infL_total {I : Set (List (Move E (F₁ ⊕ₛ F₂)))} (hI : IsInfPlay I) {s t : List (Move E F₁)}
    (hs : s ∈ infL I) (ht : t ∈ infL I) : s <+: t ∨ t <+: s := by
  obtain ⟨p, hp, hs⟩ := hs
  obtain ⟨p', hp', ht⟩ := ht
  rcases hI.total hp hp' with h | h
  · exact List.prefix_or_prefix_of_prefix (hs.trans (halves_prefix h false).1) ht
  · exact List.prefix_or_prefix_of_prefix hs (ht.trans (halves_prefix h false).1)

theorem infR_total {I : Set (List (Move E (F₁ ⊕ₛ F₂)))} (hI : IsInfPlay I) {s t : List (Move E F₂)}
    (hs : s ∈ infR I) (ht : t ∈ infR I) : s <+: t ∨ t <+: s := by
  obtain ⟨p, hp, hs⟩ := hs
  obtain ⟨p', hp', ht⟩ := ht
  rcases hI.total hp hp' with h | h
  · exact List.prefix_or_prefix_of_prefix (hs.trans (halves_prefix h false).2) ht
  · exact List.prefix_or_prefix_of_prefix hs (ht.trans (halves_prefix h false).2)

/-- The left projection of an infinite trace is infinite iff its left halves are unbounded. -/
theorem isInfPlay_infL_iff {I : Set (List (Move E (F₁ ⊕ₛ F₂)))} (hI : IsInfPlay I) :
    IsInfPlay (infL I) ↔ ∀ k, ∃ p ∈ I, k ≤ (halves false p).1.length := by
  refine ⟨fun h k => ?_, fun h => ⟨?_, infL_total hI, fun k => ?_⟩⟩
  · obtain ⟨s, ⟨p, hp, hs⟩, hk⟩ := h.unbounded k
    exact ⟨p, hp, hk.trans hs.length_le⟩
  · rintro s t ⟨p, hp, ht⟩ hs
    exact ⟨p, hp, hs.trans ht⟩
  · obtain ⟨p, hp, hk⟩ := h k
    exact ⟨_, ⟨p, hp, List.prefix_refl _⟩, hk⟩

/-- The right projection of an infinite trace is infinite iff its right halves are unbounded. -/
theorem isInfPlay_infR_iff {I : Set (List (Move E (F₁ ⊕ₛ F₂)))} (hI : IsInfPlay I) :
    IsInfPlay (infR I) ↔ ∀ k, ∃ p ∈ I, k ≤ (halves false p).2.length := by
  refine ⟨fun h k => ?_, fun h => ⟨?_, infR_total hI, fun k => ?_⟩⟩
  · obtain ⟨s, ⟨p, hp, hs⟩, hk⟩ := h.unbounded k
    exact ⟨p, hp, hk.trans hs.length_le⟩
  · rintro s t ⟨p, hp, ht⟩ hs
    exact ⟨p, hp, hs.trans ht⟩
  · obtain ⟨p, hp, hk⟩ := h k
    exact ⟨_, ⟨p, hp, List.prefix_refl _⟩, hk⟩

/-- An infinite trace has an infinite projection. -/
theorem isInfPlay_infL_or_infR {I : Set (List (Move E (F₁ ⊕ₛ F₂)))} (hI : IsInfPlay I) :
    IsInfPlay (infL I) ∨ IsInfPlay (infR I) := by
  rw [isInfPlay_infL_iff hI, isInfPlay_infR_iff hI]
  by_contra h
  simp only [not_or, not_forall, not_exists, not_and, not_le] at h
  obtain ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩⟩ := h
  obtain ⟨p, hp, hk⟩ := hI.unbounded (k₁ + k₂)
  have := halves_length false p
  have := h₁ p hp
  have := h₂ p hp
  omega

/-! ## Lifting one side -/

/-- The position of a component as a position of the pairing. -/
def posL : Pos E F₁ → Pos E (F₁ ⊕ₛ F₂)
  | .idle => .idle
  | .run q => .run (.inl q)
  | .wait q m => .wait (.inl q) m

/-- The position of a component as a position of the pairing. -/
def posR : Pos E F₂ → Pos E (F₁ ⊕ₛ F₂)
  | .idle => .idle
  | .run q => .run (.inr q)
  | .wait q m => .wait (.inr q) m

theorem path_map_liftL {x y : Pos E F₁} {s : List (Move E F₁)} (h : Path x s y) :
    Path (posL (F₂ := F₂) x) (s.map liftL) (posL y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (by cases h <;> constructor) ih

theorem path_map_liftR {x y : Pos E F₂} {s : List (Move E F₂)} (h : Path x s y) :
    Path (posR (F₁ := F₁) x) (s.map liftR) (posR y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (by cases h <;> constructor) ih

theorem legal_map_liftL {s : List (Move E F₁)} (h : Legal s) : Legal (s.map (liftL (F₂ := F₂))) :=
  let ⟨_, h⟩ := h; ⟨_, path_map_liftL h⟩

theorem legal_map_liftR {s : List (Move E F₂)} (h : Legal s) : Legal (s.map (liftR (F₁ := F₁))) :=
  let ⟨_, h⟩ := h; ⟨_, path_map_liftR h⟩

/-- The halves of a lifted left play. -/
theorem halves_map_liftL (s : List (Move E F₁)) :
    halves false (s.map (liftL (F₂ := F₂))) = (s, []) := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    rcases x with e | (q | ⟨q, r⟩) <;> simp [liftL, halves, ih]

theorem halves_true_map_liftR (s : List (Move E F₂)) :
    halves true (s.map (liftR (F₁ := F₁))) = ([], s) := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    rcases x with e | (q | ⟨q, r⟩) <;> simp [liftR, halves, ih]

/-- The halves of a lifted legal right play. -/
theorem halves_map_liftR {s : List (Move E F₂)} (h : Legal s) :
    halves false (s.map (liftR (F₁ := F₁))) = ([], s) := by
  rcases s with _ | ⟨o, s⟩
  · rfl
  obtain ⟨_, h⟩ := h
  cases h with
  | cons h _ =>
    cases h with
    | ask q =>
      simp only [List.map_cons, liftR, halves, halves_true_map_liftR]

/-- The image of an infinite trace under a map of moves. -/
theorem isInfPlay_image {α β : Type u} (f : α → β) {I : Set (List α)} (hI : IsInfPlay I) :
    IsInfPlay (List.map f '' I) where
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

theorem not_isInfPlay_of_subset_nil {α : Type u} {J : Set (List α)} (h : J ⊆ {[]}) :
    ¬ IsInfPlay J := fun hJ => by
  obtain ⟨s, hs, hk⟩ := hJ.unbounded 1
  rw [h hs] at hk
  exact absurd hk (by simp)

/-- An infinite play of the left component, lifted, is an infinite play of the pairing. -/
theorem inf_map_liftL (σ₁ : DStrategy E F₁) (σ₂ : DStrategy E F₂) {I : Set (List (Move E F₁))}
    (hI : I ∈ σ₁.inf) : List.map (liftL (F₂ := F₂)) '' I ∈ (σ₁.pair σ₂).inf := by
  have hI' := σ₁.inf_isInf hI
  have hL : infL (List.map (liftL (F₂ := F₂)) '' I) = I := by
    ext s
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hs⟩
      rw [halves_map_liftL] at hs
      exact hI'.of_prefix hp hs
    · intro hs
      exact ⟨_, ⟨s, hs, rfl⟩, by rw [halves_map_liftL]; exact List.prefix_refl _⟩
  refine ⟨isInfPlay_image _ hI', ?_, fun _ => by rw [hL]; exact hI, fun h => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hp' := σ₁.inf_sub hI hp
    refine ⟨legal_map_liftL (σ₁.toStrategy.legal hp'), ?_⟩
    rw [halves_map_liftL]
    exact ⟨hp', σ₂.toStrategy.nil_mem⟩
  · refine (not_isInfPlay_of_subset_nil ?_ h).elim
    rintro s ⟨_, ⟨p, -, rfl⟩, hs⟩
    rw [halves_map_liftL] at hs
    exact List.prefix_nil.1 hs

/-- An infinite play of the right component, lifted, is an infinite play of the pairing. -/
theorem inf_map_liftR (σ₁ : DStrategy E F₁) (σ₂ : DStrategy E F₂) {I : Set (List (Move E F₂))}
    (hI : I ∈ σ₂.inf) : List.map (liftR (F₁ := F₁)) '' I ∈ (σ₁.pair σ₂).inf := by
  have hI' := σ₂.inf_isInf hI
  have hl : ∀ {p}, p ∈ I → halves false (p.map (liftR (F₁ := F₁))) = ([], p) := fun hp =>
    halves_map_liftR (σ₂.toStrategy.legal (σ₂.inf_sub hI hp))
  have hR : infR (List.map (liftR (F₁ := F₁)) '' I) = I := by
    ext s
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hs⟩
      rw [hl hp] at hs
      exact hI'.of_prefix hp hs
    · intro hs
      exact ⟨_, ⟨s, hs, rfl⟩, by rw [hl hs]; exact List.prefix_refl _⟩
  refine ⟨isInfPlay_image _ hI', ?_, fun h => ?_, fun _ => by rw [hR]; exact hI⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hp' := σ₂.inf_sub hI hp
    refine ⟨legal_map_liftR (σ₂.toStrategy.legal hp'), ?_⟩
    rw [hl hp]
    exact ⟨σ₁.toStrategy.nil_mem, hp'⟩
  · refine (not_isInfPlay_of_subset_nil ?_ h).elim
    rintro s ⟨_, ⟨p, hp, rfl⟩, hs⟩
    rw [hl hp] at hs
    exact List.prefix_nil.1 hs

/-- A lifted play of the left component is a play of the pairing. -/
theorem mem_pair_map_liftL {σ₁ : Strategy E F₁} (σ₂ : Strategy E F₂) {s : List (Move E F₁)}
    (hs : s ∈ σ₁) : s.map (liftL (F₂ := F₂)) ∈ σ₁.pair σ₂ := by
  refine ⟨legal_map_liftL (σ₁.legal hs), ?_⟩
  rw [halves_map_liftL]
  exact ⟨hs, σ₂.nil_mem⟩

/-- A lifted play of the right component is a play of the pairing. -/
theorem mem_pair_map_liftR (σ₁ : Strategy E F₁) {σ₂ : Strategy E F₂} {s : List (Move E F₂)}
    (hs : s ∈ σ₂) : s.map (liftR (F₁ := F₁)) ∈ σ₁.pair σ₂ := by
  refine ⟨legal_map_liftR (σ₂.legal hs), ?_⟩
  rw [halves_map_liftR (σ₂.legal hs)]
  exact ⟨σ₁.nil_mem, hs⟩

theorem div_map_liftL {σ₁ : DStrategy E F₁} (σ₂ : DStrategy E F₂) {s : List (Move E F₁)}
    (hs : s ∈ σ₁.div) : s.map (liftL (F₂ := F₂)) ∈ (σ₁.pair σ₂).div :=
  ⟨mem_pair_map_liftL σ₂.toStrategy (σ₁.div_mem hs),
    .inl (by rw [halves_map_liftL]; exact hs)⟩

theorem div_map_liftR (σ₁ : DStrategy E F₁) {σ₂ : DStrategy E F₂} {s : List (Move E F₂)}
    (hs : s ∈ σ₂.div) : s.map (liftR (F₁ := F₁)) ∈ (σ₁.pair σ₂).div :=
  ⟨mem_pair_map_liftR σ₁.toStrategy (σ₂.div_mem hs), .inr (by
    rw [halves_map_liftR (σ₂.toStrategy.legal (σ₂.div_mem hs))]
    exact hs)⟩

theorem pair_mono {σ₁ τ₁ : DStrategy E F₁} {σ₂ τ₂ : DStrategy E F₂} (h₁ : σ₁ ≤ τ₁)
    (h₂ : σ₂ ≤ τ₂) : σ₁.pair σ₂ ≤ τ₁.pair τ₂ :=
  ⟨Strategy.pair_mono h₁.1 h₂.1, fun _ ⟨hp, h⟩ => ⟨Strategy.pair_mono h₁.1 h₂.1 hp,
    h.imp (fun h => h₁.2.1 h) (fun h => h₂.2.1 h)⟩, fun _ ⟨hI, hs, hl, hr⟩ =>
    ⟨hI, fun _ h => Strategy.pair_mono h₁.1 h₂.1 (hs h), fun h => h₁.2.2 (hl h),
      fun h => h₂.2.2 (hr h)⟩⟩

/-- A divergent play of the pairing diverges on its current side. -/
theorem mem_div_pair_iff {σ₁ : DStrategy E F₁} {σ₂ : DStrategy E F₂}
    {p : List (Move E (F₁ ⊕ₛ F₂))} :
    p ∈ (σ₁.pair σ₂).div ↔ p ∈ σ₁.toStrategy.pair σ₂.toStrategy ∧
      ((side false p = false ∧ (halves false p).1 ∈ σ₁.div) ∨
        (side false p = true ∧ (halves false p).2 ∈ σ₂.div)) := by
  refine ⟨fun ⟨hp, h⟩ => ⟨hp, ?_⟩, fun ⟨hp, h⟩ => ⟨hp, h.imp And.right And.right⟩⟩
  rcases h with h | h
  · obtain ⟨q, hq⟩ := σ₁.div_run h
    exact .inl ⟨(run_of_halves_left hp.1 hq).1, h⟩
  · obtain ⟨q, hq⟩ := σ₂.div_run h
    exact .inr ⟨(run_of_halves_right hp.1 hq).1, h⟩

/-- Pairing the least readings gives the least reading of the pairing. -/
theorem pair_ofStrategy (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (DStrategy.ofStrategy σ₁).pair (DStrategy.ofStrategy σ₂) =
      DStrategy.ofStrategy (σ₁.pair σ₂) := by
  refine DStrategy.ext rfl ?_ ?_
  · ext p
    simp only [DStrategy.pair, DStrategy.ofStrategy, Set.mem_empty_iff_false, or_self,
      and_false, Set.mem_ofPred_eq]
  · ext I
    simp only [DStrategy.ofStrategy, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hI, -, h₁, h₂⟩
    rcases isInfPlay_infL_or_infR hI with h | h
    · exact h₁ h
    · exact h₂ h

end Silmaril.Proofs.Games.DPair
