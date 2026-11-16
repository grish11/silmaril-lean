module

public import Silmaril.Formats.JsonLines.Defs
public import Silmaril.Formats.JsonBytes.Depth.Thms
public import Silmaril.Formats.JsonBytes.Thms
public import Silmaril.Formats.Utf8.Thms
public import Silmaril.Semantics.StreamBounds.Thms

/-! # Proofs: JSON Lines over bytes (`Silmaril.Formats.JsonLines.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonLines

open Silmaril.Formats.JsonLines

theorem lf_ne_cr : lf ≠ cr := by decide

theorem not_mem_lf_of_mem_lineOf {pol : Policy} {L : Language UInt8} {w : List UInt8}
    (h : w ∈ lineOf pol L) : lf ∉ w := by
  rcases h with ⟨rfl, -⟩ | ⟨-, hw, -⟩ | ⟨-, t, ht, hlf, -, -⟩
  · simp
  · exact hw
  · rcases ht with rfl | rfl
    · exact hlf
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hlf, lf_ne_cr⟩

theorem lineOf_mono {pol : Policy} {L L' : Language UInt8} (h : L ≤ L') :
    lineOf pol L ≤ lineOf pol L' := by
  rintro w (hb | ⟨hc, hw, hL⟩ | ⟨hc, t, ht, h1, h2, hL⟩)
  · exact Or.inl hb
  · exact Or.inr (Or.inl ⟨hc, hw, h hL⟩)
  · exact Or.inr (Or.inr ⟨hc, t, ht, h1, h2, h hL⟩)

theorem frameLang_mono {pol : Policy} {L L' : Language UInt8} (h : L ≤ L') :
    frameLang pol L ≤ frameLang pol L' := by
  rintro w ⟨lines, hl, hw⟩
  exact ⟨lines, fun l hm => lineOf_mono h (hl l hm), hw⟩

/-! ## Deciding lines -/

theorem contains_eq_false {w : List UInt8} {a : UInt8} : (!w.contains a) = true ↔ a ∉ w := by
  simp

theorem textLineB_iff {c : Bool} {ok : List UInt8 → Bool} {L : Language UInt8}
    (hok : ∀ w, ok w = true ↔ w ∈ L) {w : List UInt8} :
    textLineB c ok w = true ↔ w ∈ textLine c L := by
  cases c with
  | true =>
    simp only [textLineB, ite_true, Bool.and_eq_true, contains_eq_false, hok, textLine]
    simp only [true_and, Bool.true_eq_false, false_and, or_false]
    exact Iff.rfl
  | false =>
    simp only [textLineB, Bool.false_eq_true, ite_false, textLine]
    by_cases hl : w.getLast? = some cr
    · simp only [hl, ite_true, Bool.and_eq_true, contains_eq_false, hok]
      have hw : w = w.dropLast ++ [cr] := (List.dropLast_append_getLast? cr hl).symm
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact Or.inr ⟨trivial, w.dropLast, Or.inr hw, h1, h2, h3⟩
      · rintro (⟨h, -⟩ | ⟨-, t, ht, h1, h2, h3⟩)
        · exact absurd h (by decide)
        rcases ht with rfl | rfl
        · exact absurd (List.mem_of_getLast? hl) h2
        · simp only [List.dropLast_concat]
          exact ⟨⟨h1, h2⟩, h3⟩
    · simp only [hl, ite_false, Bool.and_eq_true, contains_eq_false, hok]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact Or.inr ⟨trivial, w, Or.inl rfl, h1, h2, h3⟩
      · rintro (⟨h, -⟩ | ⟨-, t, ht, h1, h2, h3⟩)
        · exact absurd h (by decide)
        rcases ht with rfl | rfl
        · exact ⟨⟨h1, h2⟩, h3⟩
        · exact absurd (by simp) hl

theorem lineOfB_iff {pol : Policy} {ok : List UInt8 → Bool} {L : Language UInt8}
    (hok : ∀ w, ok w = true ↔ w ∈ L) {w : List UInt8} :
    lineOfB pol ok w = true ↔ w ∈ lineOf pol L := by
  simp only [lineOfB, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff, textLineB_iff hok]
  rfl

/-! ## Splitting at line feeds -/

theorem mem_joined_iff {pol : Policy} {L : Language UInt8} {w : List UInt8} :
    (∃ lines : List (List UInt8), (∀ l ∈ lines, l ∈ lineOf pol L) ∧ w = joined lines) ↔
      w = [] ∨ ∀ l ∈ w.splitOn lf, l ∈ lineOf pol L := by
  constructor
  · rintro ⟨lines, hl, rfl⟩
    by_cases hn : lines = []
    · subst hn; exact Or.inl rfl
    · right
      rw [joined, List.splitOn_intercalate lf (fun l hm => not_mem_lf_of_mem_lineOf (hl l hm)) hn]
      exact hl
  · rintro (rfl | h)
    · exact ⟨[], by simp, rfl⟩
    · exact ⟨w.splitOn lf, h, (List.intercalate_splitOn lf).symm⟩

theorem mem_terminated_iff {pol : Policy} {L : Language UInt8} {w : List UInt8} :
    (∃ lines : List (List UInt8), (∀ l ∈ lines, l ∈ lineOf pol L) ∧ w = terminated lines) ↔
      (w.splitOn lf).getLast? = some [] ∧ ∀ l ∈ (w.splitOn lf).dropLast, l ∈ lineOf pol L := by
  constructor
  · rintro ⟨lines, hl, rfl⟩
    have hx : ∀ l ∈ lines ++ [[]], lf ∉ l := by
      intro l hm
      rcases List.mem_append.mp hm with hm | hm
      · exact not_mem_lf_of_mem_lineOf (hl l hm)
      · simp at hm; simp [hm]
    rw [terminated, List.splitOn_intercalate lf hx (by simp)]
    simp only [List.getLast?_concat, List.dropLast_concat, true_and]
    exact hl
  · rintro ⟨hlast, h⟩
    refine ⟨(w.splitOn lf).dropLast, h, ?_⟩
    rw [terminated, List.dropLast_append_getLast? _ hlast]
    exact (List.intercalate_splitOn lf).symm

theorem splitLf_eq (w : List UInt8) : splitLf w = w.splitOn lf := by
  induction w with
  | nil => rw [List.splitOn_nil]; rfl
  | cons b w ih =>
    rw [splitLf, ih, List.splitOn_cons_eq_ite_modifyHead]

theorem frameB_iff {pol : Policy} {ok : List UInt8 → Bool} {L : Language UInt8}
    (hok : ∀ w, ok w = true ↔ w ∈ L) {w : List UInt8} :
    frameB pol ok w = true ↔ w ∈ frameLang pol L := by
  simp only [frameB, splitLf_eq]
  have hall : ∀ ls : List (List UInt8),
      ls.all (lineOfB pol ok) = true ↔ ∀ l ∈ ls, l ∈ lineOf pol L := fun ls => by
    simp [List.all_eq_true, lineOfB_iff hok]
  have req : (decide ((w.splitOn lf).getLast? = some []) &&
      (w.splitOn lf).dropLast.all (lineOfB pol ok)) = true ↔
      ∃ lines : List (List UInt8), (∀ l ∈ lines, l ∈ lineOf pol L) ∧ w = terminated lines := by
    rw [mem_terminated_iff, Bool.and_eq_true, decide_eq_true_iff, hall]
  have forb : (w.isEmpty || (w.splitOn lf).all (lineOfB pol ok)) = true ↔
      ∃ lines : List (List UInt8), (∀ l ∈ lines, l ∈ lineOf pol L) ∧ w = joined lines := by
    rw [mem_joined_iff, Bool.or_eq_true, List.isEmpty_iff, hall]
  obtain ⟨final, blank, c⟩ := pol
  cases final with
  | required =>
    rw [req]
    rfl
  | forbidden =>
    rw [forb]
    rfl
  | optional =>
    rw [Bool.or_eq_true, req, forb]
    constructor
    · rintro (⟨ls, hl, h⟩ | ⟨ls, hl, h⟩)
      exacts [⟨ls, hl, Or.inl h⟩, ⟨ls, hl, Or.inr h⟩]
    · rintro ⟨ls, hl, h | h⟩
      exacts [Or.inl ⟨ls, hl, h⟩, Or.inr ⟨ls, hl, h⟩]

/-! ## Framing and generic item bounds -/

theorem intercalate_cons_of_ne_nil {s a : List UInt8} {ls : List (List UInt8)} (h : ls ≠ []) :
    s.intercalate (a :: ls) = a ++ s ++ s.intercalate ls := by
  obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil h
  exact List.intercalate_cons_cons

theorem terminated_eq_frameItems (lines : List (List UInt8)) :
    terminated lines = Silmaril.Streams.frameItems lf lines := by
  induction lines with
  | nil => rfl
  | cons a t ih =>
    rw [terminated, List.cons_append, intercalate_cons_of_ne_nil (by simp), ← terminated, ih]
    simp [Silmaril.Streams.frameItems]

theorem terminated_mem_itemBound_iff {pol : Policy} {L : Language UInt8}
    {lines : List (List UInt8)} (hl : ∀ l ∈ lines, l ∈ lineOf pol L) (n : ℕ) :
    terminated lines ∈ Silmaril.Streams.ItemBound (· == lf) n ↔
      lines ∈ Silmaril.Accept.itemsWithin List.length n := by
  rw [terminated_eq_frameItems]
  refine Silmaril.Streams.frameItems_mem_itemBound_iff (by simp) lines ?_
  intro x hx a ha
  have := not_mem_lf_of_mem_lineOf (hl x hx)
  simp only [beq_eq_false_iff_ne, ne_eq]
  rintro rfl
  exact this ha

/-! ## UTF-8 -/

open Silmaril.Formats.Utf8 in
theorem intercalate_isWellFormed {ls : List (List UInt8)} (h : ∀ l ∈ ls, IsWellFormed l) :
    IsWellFormed ([lf].intercalate ls) := by
  induction ls with
  | nil => exact isWellFormed_nil
  | cons a t ih =>
    by_cases ht : t = []
    · subst ht; simpa using h a (by simp)
    · rw [intercalate_cons_of_ne_nil ht]
      exact isWellFormed_append (isWellFormed_append (h a (by simp))
        (isWellFormed_of_ascii (by decide))) (ih fun l hl => h l (by simp [hl]))

open Silmaril.Formats.Utf8 in
theorem lineOf_isWellFormed {pol : Policy} {p : Silmaril.Formats.JsonBytes.Profile}
    {w : List UInt8} (h : w ∈ lineOf pol (Silmaril.Formats.JsonBytes.language p)) :
    IsWellFormed w := by
  rcases h with ⟨rfl, -⟩ | ⟨-, -, hL⟩ | ⟨-, t, ht, -, -, hL⟩
  · exact isWellFormed_nil
  · exact Silmaril.Formats.JsonBytes.language_isWellFormed hL
  · rcases ht with rfl | rfl
    · exact Silmaril.Formats.JsonBytes.language_isWellFormed hL
    · exact isWellFormed_append (Silmaril.Formats.JsonBytes.language_isWellFormed hL)
        (isWellFormed_of_ascii (by decide))

theorem language_isWellFormed {pol : Policy} {p : Silmaril.Formats.JsonBytes.Profile}
    {w : List UInt8} (h : w ∈ language pol p) : Silmaril.Formats.Utf8.IsWellFormed w := by
  obtain ⟨lines, hl, hw⟩ := h
  have hj := intercalate_isWellFormed (ls := lines) fun l hm => lineOf_isWellFormed (hl l hm)
  have ht := intercalate_isWellFormed (ls := lines ++ [[]]) fun l hm => by
    rcases List.mem_append.mp hm with hm | hm
    · exact lineOf_isWellFormed (hl l hm)
    · simp at hm; subst hm; exact Silmaril.Formats.Utf8.isWellFormed_nil
  obtain ⟨final, blank, c⟩ := pol
  cases final with
  | required => exact hw ▸ ht
  | forbidden => exact hw ▸ hj
  | optional => rcases hw with hw | hw; exacts [hw ▸ ht, hw ▸ hj]

/-! ## Depth -/

theorem exists_lineOf_languageAt {pol : Policy} {p : Silmaril.Formats.JsonBytes.Profile}
    {w : List UInt8} (h : w ∈ lineOf pol (Silmaril.Formats.JsonBytes.language p)) :
    ∃ d, w ∈ lineOf pol (Silmaril.Formats.JsonBytes.languageAt p d) := by
  have key : ∀ {t}, t ∈ Silmaril.Formats.JsonBytes.language p →
      ∃ d, t ∈ Silmaril.Formats.JsonBytes.languageAt p d := fun {t} ht => by
    rw [← Silmaril.Formats.JsonBytes.iUnion_languageAt] at ht
    exact Set.mem_iUnion.mp ht
  rcases h with hb | ⟨hc, hw, hL⟩ | ⟨hc, t, ht, h1, h2, hL⟩
  · exact ⟨0, Or.inl hb⟩
  · obtain ⟨d, hd⟩ := key hL; exact ⟨d, Or.inr (Or.inl ⟨hc, hw, hd⟩)⟩
  · obtain ⟨d, hd⟩ := key hL; exact ⟨d, Or.inr (Or.inr ⟨hc, t, ht, h1, h2, hd⟩)⟩

theorem iUnion_languageAt (pol : Policy) (p : Silmaril.Formats.JsonBytes.Profile) :
    (⋃ d, (languageAt pol p d : Set (List UInt8))) = language pol p := by
  ext w
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp h
    exact frameLang_mono (Silmaril.Formats.JsonBytes.languageAt_le_language p d) hd
  · rintro ⟨lines, hl, hw⟩
    have : ∃ d, ∀ l ∈ lines, l ∈ lineOf pol (Silmaril.Formats.JsonBytes.languageAt p d) := by
      clear hw
      induction lines with
      | nil => exact ⟨0, by simp⟩
      | cons a t ih =>
        obtain ⟨d, hd⟩ := exists_lineOf_languageAt (hl a (by simp))
        obtain ⟨e, he⟩ := ih fun l hm => hl l (by simp [hm])
        refine ⟨max d e, ?_⟩
        intro l hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact lineOf_mono (Silmaril.Formats.JsonBytes.languageAt_mono (le_max_left _ _)) hd
        · exact lineOf_mono (Silmaril.Formats.JsonBytes.languageAt_mono (le_max_right _ _))
            (he l hm)
    obtain ⟨d, hd⟩ := this
    exact Set.mem_iUnion.mpr ⟨d, lines, hd, hw⟩

end Silmaril.Proofs.Formats.JsonLines

end
