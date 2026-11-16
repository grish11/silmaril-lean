module

public import Silmaril.Games.AnsPull.Defs
public import Silmaril.Games.DPair.Thms
public import Silmaril.Games.Div.Thms

/-!
# Pulling back along move maps: limits, pairing and inverse relabellings (proofs)

* `isInfPlay_image`: the image of an infinite trace along a map of moves is an infinite trace;
  `lim_map`: the limit of a chain mapped is the mapped limit.
* `pull_limits`: pulling back the divergence-free reading with every limit gives the same reading
  of the pulled-back strategy.
* `pull_pair`: a move map that acts on the halves of a pairing (`Split.halves`) pulls the pairing
  back to the pairing of the pullbacks.
* `halves_lowMove`, `halves_ansMove`: the lower relabelling and the side-by-side upper
  relabelling act on halves.
* `mapAns_eq_pull`: relabelling along an invertible family is pulling back along the inverse.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.AnsPull

open Silmaril.Games

universe u v

theorem isInfPlay_image {α β : Type v} (f : α → β) {I : Set (List α)} (hI : IsInfPlay I) :
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
  unbounded n := by
    obtain ⟨s, hs, hn⟩ := hI.unbounded n
    exact ⟨_, ⟨s, hs, rfl⟩, by simpa using hn⟩

theorem lim_map {α β : Type v} (f : α → β) (c : Chain α) :
    Chain.lim (fun n => (c n).map f) = List.map f '' c.lim := by
  ext q
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨(c n).take q.length, ⟨n, List.take_prefix _ _⟩, ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hn).symm
  · rintro ⟨q', ⟨n, hn⟩, rfl⟩
    exact ⟨n, hn.map _⟩

variable {E F E' F' : Sig.{u}}

theorem path_map {f : Move E F → Move E' F'} {pf : Pos E F → Pos E' F'} (hf : PullData f pf)
    {x y : Pos E F} {s : List (Move E F)} (h : Path x s y) : Path (pf x) (s.map f) (pf y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (hf.step h) ih

theorem legal_map {f : Move E F → Move E' F'} {pf : Pos E F → Pos E' F'} (hf : PullData f pf)
    {s : List (Move E F)} (h : Legal s) : Legal (s.map f) := by
  obtain ⟨y, hy⟩ := h
  have := path_map hf hy
  rw [hf.idle] at this
  exact ⟨_, this⟩

theorem pull_limits {f : Move E F → Move E' F'} {pf : Pos E F → Pos E' F'} (hf : PullData f pf)
    (σ : Strategy E' F') :
    (DStrategy.limits σ).pull f pf hf = DStrategy.limits (σ.pull f pf hf) := by
  refine DStrategy.ext rfl ?_ ?_
  · ext p
    exact ⟨fun h => h.elim, fun h => h.elim⟩
  · ext J
    constructor
    · rintro ⟨hJ, -, hsub⟩
      exact ⟨hJ, fun p hp => hsub ⟨p, hp, rfl⟩⟩
    · rintro ⟨hJ, hsub⟩
      exact ⟨hJ, isInfPlay_image f hJ, by rintro _ ⟨p, hp, rfl⟩; exact hsub hp⟩

section Pair

variable {F₁ F₂ F₁' F₂' : Sig.{u}} {f : Move E (F₁ ⊕ₛ F₂) → Move E' (F₁' ⊕ₛ F₂')}
  {pf : Pos E (F₁ ⊕ₛ F₂) → Pos E' (F₁' ⊕ₛ F₂')} {f₁ : Move E F₁ → Move E' F₁'}
  {pf₁ : Pos E F₁ → Pos E' F₁'} {f₂ : Move E F₂ → Move E' F₂'} {pf₂ : Pos E F₂ → Pos E' F₂'}

theorem infL_image (hh : ∀ p, Split.halves false (p.map f) =
      ((Split.halves false p).1.map f₁, (Split.halves false p).2.map f₂))
    (J : Set (List (Move E (F₁ ⊕ₛ F₂)))) :
    Split.infL (List.map f '' J) = List.map f₁ '' Split.infL J := by
  ext s
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hs⟩
    rw [hh] at hs
    refine ⟨(Split.halves false p).1.take s.length, ⟨p, hp, List.take_prefix _ _⟩, ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hs).symm
  · rintro ⟨s, ⟨p, hp, hs⟩, rfl⟩
    refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    rw [hh]
    exact hs.map _

theorem infR_image (hh : ∀ p, Split.halves false (p.map f) =
      ((Split.halves false p).1.map f₁, (Split.halves false p).2.map f₂))
    (J : Set (List (Move E (F₁ ⊕ₛ F₂)))) :
    Split.infR (List.map f '' J) = List.map f₂ '' Split.infR J := by
  ext s
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hs⟩
    rw [hh] at hs
    refine ⟨(Split.halves false p).2.take s.length, ⟨p, hp, List.take_prefix _ _⟩, ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hs).symm
  · rintro ⟨s, ⟨p, hp, hs⟩, rfl⟩
    refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    rw [hh]
    exact hs.map _

theorem pull_pair (hf : PullData f pf) (hf₁ : PullData f₁ pf₁) (hf₂ : PullData f₂ pf₂)
    (hh : ∀ p, Split.halves false (p.map f) =
      ((Split.halves false p).1.map f₁, (Split.halves false p).2.map f₂))
    (σ₁ : DStrategy E' F₁') (σ₂ : DStrategy E' F₂') :
    (σ₁.pair σ₂).pull f pf hf = (σ₁.pull f₁ pf₁ hf₁).pair (σ₂.pull f₂ pf₂ hf₂) := by
  have hS : ∀ p, p.map f ∈ (σ₁.pair σ₂).toStrategy ↔
      p ∈ ((σ₁.pull f₁ pf₁ hf₁).pair (σ₂.pull f₂ pf₂ hf₂)).toStrategy := fun p => by
    have e := hh p
    constructor
    · intro h
      have hl : Legal p := ((σ₁.pair σ₂).pull f pf hf).toStrategy.legal h
      obtain ⟨-, h₁, h₂⟩ := h
      rw [e] at h₁ h₂
      exact ⟨hl, h₁, h₂⟩
    · rintro ⟨hl, h₁, h₂⟩
      refine ⟨legal_map hf hl, ?_, ?_⟩
      · rw [e]; exact h₁
      · rw [e]; exact h₂
  have hlen₁ : ∀ p : List (Move E (F₁ ⊕ₛ F₂)),
      (Split.halves false (p.map f)).1.length = (Split.halves false p).1.length := fun p => by
    rw [hh]; simp
  have hlen₂ : ∀ p : List (Move E (F₁ ⊕ₛ F₂)),
      (Split.halves false (p.map f)).2.length = (Split.halves false p).2.length := fun p => by
    rw [hh]; simp
  refine DStrategy.ext (Strategy.ext hS) ?_ ?_
  · ext p
    have e := hh p
    show p.map f ∈ (σ₁.pair σ₂).div ↔ _
    constructor
    · rintro ⟨hp, h⟩
      rw [e] at h
      exact ⟨(hS p).1 hp, h⟩
    · rintro ⟨hp, h⟩
      refine ⟨(hS p).2 hp, ?_⟩
      rw [e]
      exact h
  · ext J
    show IsInfPlay J ∧ List.map f '' J ∈ (σ₁.pair σ₂).inf ↔ _
    constructor
    · rintro ⟨hJ, -, hsub, hL, hR⟩
      have hJ' := isInfPlay_image f hJ
      refine ⟨hJ, fun p hp => (hS p).1 (hsub ⟨p, hp, rfl⟩), fun h => ⟨h, ?_⟩, fun h => ⟨h, ?_⟩⟩
      · rw [← infL_image hh]
        refine hL ((Split.isInfPlay_infL_iff hJ').2 fun n => ?_)
        obtain ⟨p, hp, hn⟩ := (Split.isInfPlay_infL_iff hJ).1 h n
        exact ⟨_, ⟨p, hp, rfl⟩, by rw [hlen₁]; exact hn⟩
      · rw [← infR_image hh]
        refine hR ((Split.isInfPlay_infR_iff hJ').2 fun n => ?_)
        obtain ⟨p, hp, hn⟩ := (Split.isInfPlay_infR_iff hJ).1 h n
        exact ⟨_, ⟨p, hp, rfl⟩, by rw [hlen₂]; exact hn⟩
    · rintro ⟨hJ, hsub, hL, hR⟩
      have hJ' := isInfPlay_image f hJ
      refine ⟨hJ, hJ', by rintro _ ⟨p, hp, rfl⟩; exact (hS p).2 (hsub hp), fun h => ?_,
        fun h => ?_⟩
      · rw [infL_image hh]
        refine (hL ((Split.isInfPlay_infL_iff hJ).2 fun n => ?_)).2
        obtain ⟨_, ⟨p, hp, rfl⟩, hn⟩ := (Split.isInfPlay_infL_iff hJ').1 h n
        exact ⟨p, hp, by rw [← hlen₁]; exact hn⟩
      · rw [infR_image hh]
        refine (hR ((Split.isInfPlay_infR_iff hJ).2 fun n => ?_)).2
        obtain ⟨_, ⟨p, hp, rfl⟩, hn⟩ := (Split.isInfPlay_infR_iff hJ').1 h n
        exact ⟨p, hp, by rw [← hlen₂]; exact hn⟩

end Pair

theorem halves_lowMove {F₁ F₂ : Sig.{u}} {B' : E.Op → Type u} (k : (q : E.Op) → E.Ar q → B' q)
    (b : Bool) (p : List (Move E (F₁ ⊕ₛ F₂))) :
    Split.halves b (p.map (lowMove k)) =
      ((Split.halves b p).1.map (lowMove k), (Split.halves b p).2.map (lowMove k)) := by
  induction p generalizing b with
  | nil => cases b <;> rfl
  | cons o p ih =>
    rcases o with (q | ⟨q, n⟩) | ((q | q) | ⟨q | q, n⟩) <;> cases b <;>
      simp [Split.halves, lowMove, ih]

section SumMove

variable {F₁ F₂ : Sig.{u}} {B₁ : F₁.Op → Type u} {B₂ : F₂.Op → Type u}
  (k₁ : (q : F₁.Op) → F₁.Ar q → B₁ q) (k₂ : (q : F₂.Op) → F₂.Ar q → B₂ q)

/-- `ansMove (sumAns k₁ k₂)`, landing in the sum of the relabelled signatures. -/
def sumMove : Move E (F₁ ⊕ₛ F₂) → Move E (Sig.mk F₁.Op B₁ ⊕ₛ Sig.mk F₂.Op B₂)
  | .inl e => .inl e
  | .inr (.ask a) => .inr (.ask a)
  | .inr (.ans (.inl q) n) => .inr (.ans (.inl q) (k₁ q n))
  | .inr (.ans (.inr q) n) => .inr (.ans (.inr q) (k₂ q n))

theorem ansMove_sumAns (o : Move E (F₁ ⊕ₛ F₂)) :
    ansMove (F := F₁ ⊕ₛ F₂) (B' := (Sig.mk F₁.Op B₁ ⊕ₛ Sig.mk F₂.Op B₂).Ar)
      (sumAns (B₁ := B₁) (B₂ := B₂) k₁ k₂) o = sumMove k₁ k₂ o := by
  rcases o with _ | (_ | ⟨q | q, n⟩) <;> rfl

theorem halves_sumMove (b : Bool) (p : List (Move E (F₁ ⊕ₛ F₂))) :
    Split.halves b (p.map (sumMove k₁ k₂)) =
      ((Split.halves b p).1.map (ansMove k₁), (Split.halves b p).2.map (ansMove k₂)) := by
  induction p generalizing b with
  | nil => cases b <;> rfl
  | cons o p ih =>
    rcases o with (q | ⟨q, n⟩) | ((q | q) | ⟨q | q, n⟩) <;> cases b <;>
      simp [Split.halves, sumMove, ansMove, ih]

theorem pullData_sumMove : PullData (sumMove (E := E) k₁ k₂) posAns where
  idle := rfl
  step h := by
    cases h with
    | ret q r => rcases q with q | q <;> constructor
    | _ => constructor
  lift {x o _} h := by
    rcases o with (q | ⟨q, n⟩) | (q | ⟨q | q, n⟩) <;> cases x <;> cases h <;>
      exact ⟨_, by constructor⟩
  run {x _} h := by
    cases x with
    | run q => exact ⟨q, rfl⟩
    | _ => simp [posAns] at h

end SumMove

section Inverse

variable {B' : F.Op → Type u} {k : (q : F.Op) → F.Ar q → B' q}

theorem map_inv {α β : Type u} {f : α → β} {g : β → α} (h : ∀ a, g (f a) = a) (s : List α) :
    (s.map f).map g = s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [h, ih]

/-- **Relabelling along `k` is pulling back along an inverse move map.** -/
theorem mapAns_eq_pull_of {g : Move E (Sig.mk F.Op B') → Move E F}
    {pg : Pos E (Sig.mk F.Op B') → Pos E F} (hg : PullData g pg)
    (h₁ : ∀ o, g (ansMove k o) = o) (h₂ : ∀ o, ansMove k (g o) = o) (σ : DStrategy E F) :
    σ.mapAns k = σ.pull g pg hg := by
  refine DStrategy.ext (Strategy.ext fun p => ⟨?_, fun h => ⟨_, h, map_inv h₂ p⟩⟩) ?_ ?_
  · rintro ⟨q, hq, rfl⟩
    show (q.map _).map g ∈ σ.toStrategy
    rw [map_inv h₁]
    exact hq
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      show (q.map _).map g ∈ σ.div
      rw [map_inv h₁]
      exact hq
    · exact fun h => ⟨_, h, map_inv h₂ p⟩
  · ext K
    constructor
    · rintro ⟨J, hJ, rfl⟩
      refine ⟨isInfPlay_image_ansMove k (σ.inf_isInf hJ), ?_⟩
      show List.map g '' (List.map _ '' J) ∈ σ.inf
      rw [Set.image_image]
      simp only [map_inv h₁, Set.image_id']
      exact hJ
    · rintro ⟨-, hK⟩
      refine ⟨_, hK, ?_⟩
      rw [Set.image_image]
      simp only [map_inv h₂, Set.image_id']

theorem mapAns_eq_pull {k' : (q : F.Op) → B' q → F.Ar q} (hk : ∀ q n, k' q (k q n) = n)
    (hk' : ∀ q n, k q (k' q n) = n) (σ : DStrategy E F) :
    σ.mapAns k = σ.pull (ansMove (F := Sig.mk F.Op B') k') posAns
      (pullData_ansMove (F := Sig.mk F.Op B') k') :=
  mapAns_eq_pull_of _
    (fun o => by rcases o with _ | (q | ⟨q, n⟩) <;> simp [ansMove, hk])
    (fun o => by rcases o with _ | (q | ⟨q, n⟩) <;> simp [ansMove, hk']) σ

end Inverse

end Silmaril.Proofs.Games.AnsPull
