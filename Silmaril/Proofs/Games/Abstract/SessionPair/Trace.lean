module

public import Silmaril.Games.DPair.Defs
public import Silmaril.Games.Div.Thms
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction

/-!
# Pairing sessions: traces and rounds

Generic facts used for the infinite plays of paired sessions.

* Infinite traces: one inside another are equal (`isInfPlay_eq_of_subset`); injective images
  reflect prefixes and infinite traces (`prefix_of_map_prefix`, `isInfPlay_of_image`).
* Rounds that never end: after the last idle point of a play (`last_idle`), a round that never
  returns to idle consists of lower moves only (`lows_of_never_idle`), and a move after such moves
  is lower (`le_of_prefix_lows`).
* Halves of concatenations and of lower moves (`halves_append`, `halves_lows`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionPair

open Silmaril.Games

universe u v

/-! ## Infinite traces -/

theorem isInfPlay_eq_of_subset {α : Type v} {I I' : Set (List α)} (h : IsInfPlay I)
    (h' : IsInfPlay I') (hs : I' ⊆ I) : I' = I := by
  refine hs.antisymm fun s hsI => ?_
  obtain ⟨t, ht, hl⟩ := h'.unbounded s.length
  exact h'.of_prefix ht (h.prefix_of_length_le hsI (hs ht) hl)

theorem prefix_of_map_prefix {α β : Type v} {f : α → β} (hf : Function.Injective f)
    {s t : List α} (h : s.map f <+: t.map f) : s <+: t := by
  rw [List.prefix_iff_eq_take] at h ⊢
  rw [List.length_map, ← List.map_take] at h
  exact List.map_injective_iff.2 hf h

theorem exists_of_prefix_map {α β : Type v} {f : α → β} {u : List β} {t : List α}
    (h : u <+: t.map f) : ∃ s, s <+: t ∧ u = s.map f :=
  ⟨t.take u.length, List.take_prefix _ _, by
    rw [List.map_take]; exact List.prefix_iff_eq_take.1 h⟩

theorem isInfPlay_of_image {α β : Type v} {f : α → β} (hf : Function.Injective f)
    {J : Set (List α)} (h : IsInfPlay (List.map f '' J)) : IsInfPlay J where
  of_prefix := by
    intro s t ht hst
    obtain ⟨s', hs', he⟩ := h.of_prefix ⟨t, ht, rfl⟩ (hst.map f)
    rwa [← List.map_injective_iff.2 hf he]
  total := by
    intro s t hs ht
    rcases h.total ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ with h | h
    · exact .inl (prefix_of_map_prefix hf h)
    · exact .inr (prefix_of_map_prefix hf h)
  unbounded k := by
    obtain ⟨_, ⟨s, hs, rfl⟩, hk⟩ := h.unbounded k
    exact ⟨s, hs, by simpa using hk⟩

/-! ## Rounds that never end -/

variable {E F F₁ F₂ : Sig.{u}}

/-- Lower moves. -/
abbrev lows (es : List (Ev E)) : List (Move E F) := es.map Sum.inl

theorem lows_append (es es' : List (Ev E)) :
    (lows (es ++ es') : List (Move E F)) = lows es ++ lows es' := List.map_append

/-- Lower moves from a running position never reach idle. -/
theorem ne_idle_of_lows {q : F.Op} :
    ∀ {es : List (Ev E)} {x g : Pos E F}, (x = .run q ∨ ∃ m, x = .wait q m) →
      Path x (lows es) g → g ≠ .idle := by
  intro es
  induction es with
  | nil =>
    rintro x g hx h
    cases h
    rcases hx with rfl | ⟨m, rfl⟩ <;> simp
  | cons e es ih =>
    rintro x g hx h
    cases h with
    | cons hs hp =>
      rcases hx with rfl | ⟨m, rfl⟩
      · cases hs with
        | call => exact ih (.inr ⟨_, rfl⟩) hp
      · cases hs with
        | reply => exact ih (.inl rfl) hp

/-- An ask followed by lower moves never reaches idle. -/
theorem ne_idle_of_ask_lows {q : F.Op} {es : List (Ev E)} {x g : Pos E F}
    (h : Path x (.inr (.ask q) :: lows es) g) : g ≠ .idle := by
  cases h with
  | cons hs hp =>
    cases hs
    exact ne_idle_of_lows (.inl rfl) hp

/-- A play from a running position that never returns to idle is made of lower moves. -/
theorem lows_of_never_idle {q : F.Op} :
    ∀ {w : List (Move E F)} {x : Pos E F}, (x = .run q ∨ ∃ m, x = .wait q m) →
      (∃ g, Path x w g) → (∀ w', w' <+: w → ∀ g, Path x w' g → g ≠ .idle) →
      ∃ es : List (Ev E), w = lows es := by
  intro w
  induction w with
  | nil => intro _ _ _ _; exact ⟨[], rfl⟩
  | cons o w ih =>
    rintro x hx ⟨g, h⟩ hn
    cases h with
    | cons hs hp =>
      have hn' : ∀ w', w' <+: w → ∀ g, Path _ w' g → g ≠ .idle := fun w' hw g hg =>
        hn (o :: w') (List.cons_prefix_cons.2 ⟨rfl, hw⟩) g (.cons hs hg)
      rcases hx with rfl | ⟨m, rfl⟩
      · cases hs with
        | call q m =>
          obtain ⟨es, rfl⟩ := ih (.inr ⟨m, rfl⟩) ⟨_, hp⟩ hn'
          exact ⟨.ask m :: es, rfl⟩
        | ret q r =>
          exact absurd rfl (hn [.inr (.ans q r)] (List.cons_prefix_cons.2 ⟨rfl, List.nil_prefix⟩)
            _ (.single (.ret q r)))
      · cases hs with
        | reply q m n =>
          obtain ⟨es, rfl⟩ := ih (.inl rfl) ⟨_, hp⟩ hn'
          exact ⟨.ans m n :: es, rfl⟩

/-- **The last idle point**: a legal play that ends away from idle is an idle play, a question,
and moves that never return to idle. -/
theorem last_idle {q₀ : List (Move E F)} {g : Pos E F} (h : Path .idle q₀ g) (hg : g ≠ .idle) :
    ∃ qi a w, q₀ = qi ++ .inr (.ask a) :: w ∧ Path .idle qi .idle ∧
      ∀ w', w' <+: w → ∀ g', Path .idle (qi ++ .inr (.ask a) :: w') g' → g' ≠ .idle := by
  induction q₀ using List.reverseRecOn generalizing g with
  | nil => cases h; exact absurd rfl hg
  | append_singleton r o ih =>
    obtain ⟨z, hz, hs⟩ := Path.concat_iff.1 h
    by_cases hzi : z = .idle
    · subst hzi
      cases hs with
      | ask a =>
        refine ⟨r, a, [], by simp, hz, fun w' hw g' hg' => ?_⟩
        rw [List.prefix_nil.1 hw] at hg'
        rw [Path.det hg' h]
        simp
    · obtain ⟨qi, a, w, rfl, hqi, hn⟩ := ih hz hzi
      refine ⟨qi, a, w ++ [o], by simp, hqi, fun w' hw g' hg' => ?_⟩
      rcases List.prefix_concat_iff.1 hw with rfl | hw
      · rw [Path.det hg' (by simpa using h)]
        exact hg
      · exact hn w' hw g' hg'

/-- A non-lower move cannot follow lower moves in a prefix: its position is at most that of the
last non-lower move. -/
theorem le_of_prefix_lows {z L : List (Move E F)} {o o' : Move E F} {es : List (Ev E)}
    (h : z ++ [o] <+: L ++ o' :: lows es) (ho : ∀ e, o ≠ .inl e) : z.length ≤ L.length := by
  by_contra hl
  rw [Nat.not_le] at hl
  have hi : z.length < (z ++ [o]).length := by simp
  have e₁ := h.getElem hi
  simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem_cons_zero] at e₁
  rw [List.getElem_append_right (by omega)] at e₁
  obtain ⟨k, hk⟩ : ∃ k, z.length - L.length = k + 1 := ⟨z.length - L.length - 1, by omega⟩
  simp only [hk, List.getElem_cons_succ, List.getElem_map] at e₁
  exact ho _ e₁

/-! ## Halves -/

theorem halves_append (b : Bool) (p r : List (Move E (F₁ ⊕ₛ F₂))) :
    Split.halves b (p ++ r) =
      ((Split.halves b p).1 ++ (Split.halves (Split.side b p) r).1,
        (Split.halves b p).2 ++ (Split.halves (Split.side b p) r).2) := by
  induction p generalizing b with
  | nil => rfl
  | cons x p ih =>
    rcases x with e | (q | ⟨q, r'⟩)
    · cases b <;> simp [Split.halves, Split.side, ih]
    · rcases q with q | q <;> simp [Split.halves, Split.side, ih]
    · rcases q with q | q <;> simp [Split.halves, Split.side, ih]

theorem halves_lows_false (es : List (Ev E)) :
    Split.halves false (lows es : List (Move E (F₁ ⊕ₛ F₂))) = (lows es, []) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Split.halves, ih]

theorem halves_lows_true (es : List (Ev E)) :
    Split.halves true (lows es : List (Move E (F₁ ⊕ₛ F₂))) = ([], lows es) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Split.halves, ih]

theorem halves_ask_inl (b : Bool) (a : F₁.Op) (es : List (Ev E)) :
    Split.halves b (.inr (.ask (.inl a)) :: lows es : List (Move E (F₁ ⊕ₛ F₂))) =
      (.inr (.ask a) :: lows es, []) := by
  cases b <;> simp [Split.halves, halves_lows_false]

theorem halves_ask_inr (b : Bool) (a : F₂.Op) (es : List (Ev E)) :
    Split.halves b (.inr (.ask (.inr a)) :: lows es : List (Move E (F₁ ⊕ₛ F₂))) =
      ([], .inr (.ask a) :: lows es) := by
  cases b <;> simp [Split.halves, halves_lows_true]

end Silmaril.Proofs.Games.Abstract.SessionPair
