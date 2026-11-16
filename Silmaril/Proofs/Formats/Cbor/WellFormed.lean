module

public import Silmaril.Formats.Cbor.WellFormed.Defs

/-! # Proofs: well-formed CBOR (`Silmaril.Formats.Cbor.WellFormed.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.WellFormed

open Silmaril.Formats.Cbor

/-! ## Bytes and heads -/

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp only [UInt8.toNat_ofNat', Nat.reducePow]; omega

theorem eq_ofNat_of_toNat {b : UInt8} {n : Nat} (h : b.toNat = n) : b = UInt8.ofNat n := by
  apply UInt8.toNat_inj.mp
  have := b.toNat_lt
  rw [toNat_ofNat_of_lt (by omega)]
  exact h

theorem argWidth_some {ai k : Nat} (h : argWidth ai = some k) :
    (ai = 24 ∧ k = 1) ∨ (ai = 25 ∧ k = 2) ∨ (ai = 26 ∧ k = 4) ∨ (ai = 27 ∧ k = 8) := by
  unfold argWidth at h
  split at h <;> simp_all

theorem argWidth_none {ai : Nat} (h1 : 28 ≤ ai) : argWidth ai = none := by
  unfold argWidth
  split <;> first | rfl | omega

theorem readArg_of_lt {ai : Nat} (h : ai < 24) (r : List UInt8) : readArg ai r = some (ai, r) := by
  simp [readArg, h]

theorem readArg_ext {ai k : Nat} (hw : argWidth ai = some k) {ext : List UInt8}
    (hl : ext.length = k) (r : List UInt8) :
    readArg ai (ext ++ r) = some (beNat ext, r) := by
  have := argWidth_some hw
  have h24 : ¬ ai < 24 := by omega
  simp [readArg, h24, hw, hl, List.take_left', List.drop_left']

theorem readArg_none {ai : Nat} (h : 28 ≤ ai) (r : List UInt8) : readArg ai r = none := by
  have h24 : ¬ ai < 24 := by omega
  simp [readArg, h24, argWidth_none h]

/-- A head of major type `mt < 8` decodes back to its argument. -/
theorem head_decode {mt a : Nat} {w : List UInt8} (hmt : mt < 8) (h : Head mt a w)
    (r : List UInt8) : ∃ b ext, w = b :: ext ∧ b.toNat / 32 = mt ∧ b.toNat % 32 < 28 ∧
      readArg (b.toNat % 32) (ext ++ r) = some (a, r) := by
  rcases h with ⟨ha, rfl⟩ | ⟨ai, k, ext, hw, hl, hv, rfl⟩
  · have hb := toNat_ofNat_of_lt (n := 32 * mt + a) (by omega)
    refine ⟨_, [], rfl, by omega, by omega, ?_⟩
    rw [hb, show (32 * mt + a) % 32 = a by omega]
    exact readArg_of_lt ha r
  · have := argWidth_some hw
    have hb := toNat_ofNat_of_lt (n := 32 * mt + ai) (by omega)
    refine ⟨_, ext, rfl, by omega, by omega, ?_⟩
    rw [hb, show (32 * mt + ai) % 32 = ai by omega, readArg_ext hw hl, hv]

/-- Reading an argument successfully gives a head. -/
theorem head_of_readArg {b : UInt8} {r r' : List UInt8} {a : Nat} (_hai : b.toNat % 32 < 28)
    (h : readArg (b.toNat % 32) r = some (a, r')) :
    ∃ ext, r = ext ++ r' ∧ Head (b.toNat / 32) a (b :: ext) := by
  have hb : b = UInt8.ofNat (32 * (b.toNat / 32) + b.toNat % 32) :=
    eq_ofNat_of_toNat (by omega)
  unfold readArg at h
  split at h
  · next hlt =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, Or.inl ⟨hlt, by rw [← hb]⟩⟩
  · split at h
    · next k hw =>
      split at h
      · next hk =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨r.take k, (List.take_append_drop k r).symm, Or.inr ⟨_, k, r.take k, hw, ?_, rfl, ?_⟩⟩
        · simp [hk]
        · rw [← hb]
      · simp at h
    · simp at h

theorem readArg_split {ai a : Nat} {r r' : List UInt8} (h : readArg ai r = some (a, r'))
    (h24 : ¬ ai < 24) : ∃ k e, argWidth ai = some k ∧ e.length = k ∧ r = e ++ r' := by
  unfold readArg at h
  simp only [h24, ↓reduceIte] at h
  split at h
  · next k hw =>
    split at h
    · next hk =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨k, r.take k, hw, by simp [hk], (List.take_append_drop k r).symm⟩
    · simp at h
  · simp at h

/-! ## Shapes of items -/

theorem head_length {mt a : Nat} {w : List UInt8} (h : Head mt a w) : 1 ≤ w.length := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, -, -, -, -, rfl⟩ <;> simp

/-- Every item starts with a byte other than `break`. -/
theorem item_head {x : List UInt8} (h : Item x) : ∃ b t, x = b :: t ∧ b ≠ breakByte := by
  have ne_of_head : ∀ {mt a w}, mt < 7 → Head mt a w → ∀ t,
      ∃ b t', w ++ t = b :: t' ∧ b ≠ breakByte := fun {mt a w} hmt hh t => by
    obtain ⟨b, ext, rfl, hb, -, -⟩ := head_decode (by omega) hh []
    refine ⟨b, ext ++ t, rfl, fun he => ?_⟩
    subst he
    simp [breakByte] at hb
    omega
  cases h with
  | uint hh => simpa using ne_of_head (by omega) hh []
  | nint hh => simpa using ne_of_head (by omega) hh []
  | string hm hs =>
    obtain ⟨n, hd, c, hh, -, rfl⟩ := hs
    exact ne_of_head (by omega) hh c
  | indefString hm _ =>
    refine ⟨_, _, rfl, fun he => ?_⟩
    have := congrArg UInt8.toNat he
    rw [toNat_ofNat_of_lt (by omega)] at this
    revert this; simp [breakByte]; omega
  | array hh _ => exact ne_of_head (by omega) hh _
  | indefArray _ => exact ⟨_, _, rfl, by decide⟩
  | map hh _ => exact ne_of_head (by omega) hh _
  | indefMap _ => exact ⟨_, _, rfl, by decide⟩
  | tag hh _ => exact ne_of_head (by omega) hh _
  | simple hv =>
    refine ⟨_, _, rfl, fun he => ?_⟩
    have := congrArg UInt8.toNat he
    rw [toNat_ofNat_of_lt (by omega)] at this
    revert this; simp [breakByte]; omega
  | simpleByte _ => exact ⟨_, _, rfl, by decide⟩
  | float hw h25 _ =>
    have := argWidth_some hw
    refine ⟨_, _, rfl, fun he => ?_⟩
    have := congrArg UInt8.toNat he
    rw [toNat_ofNat_of_lt (by omega)] at this
    revert this; simp [breakByte]; omega

theorem item_length {x : List UInt8} (h : Item x) : 1 ≤ x.length := by
  obtain ⟨b, t, rfl, -⟩ := item_head h
  simp

/-! ## Completeness: the checker skips exactly one item -/

theorem chunks_skip {mt : Nat} {cs : List UInt8} (hmt : mt = 2 ∨ mt = 3) (h : Chunks mt cs) :
    ∀ f r, cs.length + 1 ≤ f → skipChunks f mt (cs ++ breakByte :: r) = some r := by
  obtain ⟨parts, rfl, hp⟩ := h
  induction parts with
  | nil =>
    intro f r hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [skipChunks]
  | cons x parts ih =>
    intro f r hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨n, hd, c, hh, hc, rfl⟩ := hp x (by simp)
    obtain ⟨b, ext, rfl, hb1, hb2, hra⟩ :=
      head_decode (by omega) hh (c ++ (parts.flatten ++ breakByte :: r))
    have hne : b ≠ breakByte := by
      rintro rfl; revert hb1; simp [breakByte]; omega
    have := head_length hh
    simp only [List.flatten_cons, List.length_append, List.length_cons] at hf
    have hrest := ih (fun y hy => hp y (by simp [hy])) g r (by simp at hf ⊢; omega)
    simp only [List.flatten_cons, List.append_assoc, List.cons_append, skipChunks, hne,
      ite_false, hb1, hb2, and_self, ite_true, hra, Option.bind_some]
    simp [List.drop_left', hc, hrest]

mutual

theorem item_skip {x : List UInt8} :
    Item x → ∀ n r, 2 * x.length ≤ n → skip n (x ++ r) = some r
  | .uint hh, n, r, hn => by
    have := head_length hh
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨b, ext, rfl, hb1, hb2, hra⟩ := head_decode (by omega) hh r
    simp only [List.cons_append, skip, hb1, show ¬ b.toNat % 32 = 31 by omega, ite_false,
      show ¬ (0 = 7) by omega, hra, Option.bind_some, true_or, ite_true]
  | .nint hh, n, r, hn => by
    have := head_length hh
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨b, ext, rfl, hb1, hb2, hra⟩ := head_decode (by omega) hh r
    simp only [List.cons_append, skip, hb1, show ¬ b.toNat % 32 = 31 by omega, ite_false,
      show ¬ (1 = 7) by omega, hra, Option.bind_some, or_true, ite_true]
  | .string (mt := mt) hm hs, n, r, hn => by
    obtain ⟨a, h, c, hh, hc, rfl⟩ := hs
    have := head_length hh
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    obtain ⟨b, ext, rfl, hb1, hb2, hra⟩ := head_decode (by omega) hh (c ++ r)
    have h7 : ¬ mt = 7 := by omega
    have h01 : ¬ (mt = 0 ∨ mt = 1) := by omega
    simp only [List.cons_append, List.append_assoc, skip, hb1,
      show ¬ b.toNat % 32 = 31 by omega, ite_false, h7, hra, Option.bind_some, h01, hm, ite_true,
      List.length_append, hc, Nat.le_add_right, List.drop_left']
  | .indefString (mt := mt) (cs := cs) hm hc, n, r, hn => by
    simp only [List.length_cons, List.length_append] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hb := toNat_ofNat_of_lt (n := 32 * mt + 31) (by omega)
    simp only [List.cons_append, List.append_assoc, skip, hb,
      show (32 * mt + 31) % 32 = 31 by omega, show (32 * mt + 31) / 32 = mt by omega, ite_true, hm]
    exact chunks_skip hm hc m r (by omega)
  | .array (n := a) (h := h) (xs := xs) hh hx, n, r, hn => by
    have := head_length hh
    simp only [List.length_append] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨b, ext, rfl, hb1, hb2, hra⟩ := head_decode (by omega) hh (xs ++ r)
    simp only [List.cons_append, List.append_assoc, skip, hb1,
      show ¬ b.toNat % 32 = 31 by omega, ite_false, show ¬ (4 = 7) by omega, hra, Option.bind_some,
      show ¬ (4 = 0 ∨ 4 = 1) by omega, show ¬ (4 = 2 ∨ 4 = 3) by omega, ite_true]
    simp only [List.length_cons] at hn
    exact items_skipN hx m r (by omega)
  | .indefArray (xs := xs) hx, n, r, hn => by
    simp only [List.length_cons, List.length_append] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [List.cons_append, List.append_assoc, skip]
    simp only [show (0x9F : UInt8).toNat = 159 from rfl, show 159 % 32 = 31 from rfl,
      show 159 / 32 = 4 from rfl, ite_true, show ¬ (4 = 2 ∨ 4 = 3) by omega, ite_false]
    exact items_skipUntilBreak hx m r (by omega)
  | .map (n := a) (h := h) (xs := xs) hh hx, n, r, hn => by
    have := head_length hh
    simp only [List.length_append] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨b, ext, rfl, hb1, hb2, hra⟩ := head_decode (by omega) hh (xs ++ r)
    simp only [List.cons_append, List.append_assoc, skip, hb1,
      show ¬ b.toNat % 32 = 31 by omega, ite_false, show ¬ (5 = 7) by omega, hra, Option.bind_some,
      show ¬ (5 = 0 ∨ 5 = 1) by omega, show ¬ (5 = 2 ∨ 5 = 3) by omega, show ¬ (5 = 4) by omega,
      ite_true]
    simp only [List.length_cons] at hn
    exact items_skipN hx m r (by omega)
  | .indefMap (xs := xs) hx, n, r, hn => by
    simp only [List.length_cons, List.length_append] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [List.cons_append, List.append_assoc, skip]
    simp only [show (0xBF : UInt8).toNat = 191 from rfl, show 191 % 32 = 31 from rfl,
      show 191 / 32 = 5 from rfl, ite_true, show ¬ (5 = 2 ∨ 5 = 3) by omega,
      show ¬ (5 = 4) by omega, ite_false]
    exact items_skipPairs hx (by omega) m r (by omega)
  | .tag (n := a) (h := h) (x := x) hh hx, n, r, hn => by
    have := head_length hh
    simp only [List.length_append] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨b, ext, rfl, hb1, hb2, hra⟩ := head_decode (by omega) hh (x ++ r)
    simp only [List.cons_append, List.append_assoc, skip, hb1,
      show ¬ b.toNat % 32 = 31 by omega, ite_false, show ¬ (6 = 7) by omega, hra, Option.bind_some,
      show ¬ (6 = 0 ∨ 6 = 1) by omega, show ¬ (6 = 2 ∨ 6 = 3) by omega, show ¬ (6 = 4) by omega,
      show ¬ (6 = 5) by omega]
    simp only [List.length_cons] at hn
    exact item_skip hx m r (by omega)
  | .simple (v := v) hv, n, r, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    have hb := toNat_ofNat_of_lt (n := 0xE0 + v) (by omega)
    simp only [List.singleton_append, skip, hb,
      show (0xE0 + v) / 32 = 7 by omega, show (0xE0 + v) % 32 = v by omega, ite_false, ite_true, hv,
      show ¬ v = 31 by omega]
  | .simpleByte (v := v) hv, n, r, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp [skip, hv]
  | .float (ai := ai) (e := e) hw h25 he, n, r, hn => by
    have := argWidth_some hw
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    have hb := toNat_ofNat_of_lt (n := 0xE0 + ai) (by omega)
    simp only [List.cons_append, skip, hb,
      show (0xE0 + ai) / 32 = 7 by omega, show (0xE0 + ai) % 32 = ai by omega, ite_false, ite_true,
      show ¬ ai = 31 by omega, show ¬ ai < 24 by omega, show ¬ ai = 24 by omega, readArg_ext hw he, Option.map_some]
termination_by structural h _ _ _ => h

theorem items_skipN {k : Nat} {xs : List UInt8} :
    Items k xs → ∀ f r, 2 * xs.length + 1 ≤ f → skipN f k (xs ++ r) = some r
  | .nil, f, r, _ => by cases f <;> rfl
  | .cons (x := x) (xs := xs) hx hxs, f, r, hf => by
    have := item_length hx
    simp only [List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [List.append_assoc, skipN, item_skip hx g (xs ++ r) (by omega), Option.bind_some]
    exact items_skipN hxs g r (by omega)
termination_by structural h _ _ _ => h

theorem items_skipUntilBreak {k : Nat} {xs : List UInt8} :
    Items k xs → ∀ f r, 2 * xs.length + 1 ≤ f → skipUntilBreak f (xs ++ breakByte :: r) = some r
  | .nil, f, r, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [skipUntilBreak]
  | .cons (x := x) (xs := xs) hx hxs, f, r, hf => by
    have := item_length hx
    simp only [List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hs := item_skip hx g (xs ++ breakByte :: r) (by omega)
    have hrec := items_skipUntilBreak hxs g r (by omega)
    obtain ⟨b, t, rfl, hb⟩ := item_head hx
    simp only [List.cons_append, List.append_assoc] at hs ⊢
    simp only [skipUntilBreak, hb, ite_false, hs, Option.bind_some]
    exact hrec
termination_by structural h _ _ _ => h

theorem items_skipPairs {m : Nat} {xs : List UInt8} :
    Items m xs → m % 2 = 0 → ∀ f r, 2 * xs.length + 1 ≤ f →
      skipPairsUntilBreak f (xs ++ breakByte :: r) = some r
  | .nil, _, f, r, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [skipPairsUntilBreak]
  | .cons _ .nil, hm, _, _, _ => by omega
  | .cons (x := x) hx (.cons (x := y) (xs := xs) hy hxs), hm, f, r, hf => by
    have := item_length hx; have := item_length hy
    simp only [List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hs := item_skip hx g (y ++ xs ++ breakByte :: r) (by simp at hf ⊢; omega)
    have ht := item_skip hy g (xs ++ breakByte :: r) (by simp at hf ⊢; omega)
    have hrec := items_skipPairs hxs (by omega) g r (by simp at hf ⊢; omega)
    obtain ⟨b, t, rfl, hb⟩ := item_head hx
    simp only [List.cons_append, List.append_assoc] at hs ht ⊢
    simp only [skipPairsUntilBreak, hb, ite_false, hs, Option.bind_some, ht]
    exact hrec
termination_by structural h _ _ _ _ => h

end

/-! ## Soundness: what the checker skips is an item -/

theorem skipChunks_sound {mt : Nat} : ∀ (f : Nat) (w r : List UInt8),
    skipChunks f mt w = some r → ∃ cs, Chunks mt cs ∧ w = cs ++ breakByte :: r
  | 0, _, _, h => by simp [skipChunks] at h
  | _ + 1, [], _, h => by simp [skipChunks] at h
  | f + 1, b :: w, r, h => by
    simp only [skipChunks] at h
    split_ifs at h with hb hc
    · simp only [Option.some.injEq] at h
      subst h hb
      exact ⟨[], ⟨[], rfl, by simp⟩, rfl⟩
    · rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨a, r1⟩, hra, h⟩ := h
      split_ifs at h with hl
      obtain ⟨ext, rfl, hh⟩ := head_of_readArg hc.2 hra
      obtain ⟨cs, ⟨parts, rfl, hp⟩, he⟩ := skipChunks_sound f _ r h
      refine ⟨(b :: ext ++ r1.take a) ++ parts.flatten, ⟨(b :: ext ++ r1.take a) :: parts, rfl, ?_⟩, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨a, b :: ext, r1.take a, hc.1 ▸ hh, by simp [hl], rfl⟩
        · exact hp x hx
      · conv_lhs => rw [← List.take_append_drop a r1]
        simp [he]

mutual

theorem skip_sound : ∀ (n : Nat) (w r : List UInt8), skip n w = some r → ∃ x, Item x ∧ w = x ++ r
  | 0, _, _, h => by simp [skip] at h
  | _ + 1, [], _, h => by simp [skip] at h
  | n + 1, b :: w, r, h => by
    have hlt := b.toNat_lt
    simp only [skip] at h
    by_cases h31 : b.toNat % 32 = 31
    · simp only [h31, ↓reduceIte] at h
      by_cases h23 : b.toNat / 32 = 2 ∨ b.toNat / 32 = 3
      · simp only [h23, ↓reduceIte] at h
        obtain ⟨cs, hc, rfl⟩ := skipChunks_sound n w r h
        refine ⟨_, .indefString h23 hc, ?_⟩
        have hb : UInt8.ofNat (32 * (b.toNat / 32) + 31) = b := (eq_ofNat_of_toNat (by omega)).symm
        rw [hb]; simp
      simp only [h23, ↓reduceIte] at h
      by_cases h4 : b.toNat / 32 = 4
      · simp only [h4, ↓reduceIte] at h
        obtain ⟨k, xs, hx, rfl⟩ := skipUntilBreak_sound n w r h
        refine ⟨_, .indefArray hx, ?_⟩
        have hb : b = 0x9F := UInt8.toNat_inj.mp (by rw [show (0x9F : UInt8).toNat = 159 from rfl]; omega)
        rw [hb]; simp
      simp only [h4, ↓reduceIte] at h
      by_cases h5 : b.toNat / 32 = 5
      · simp only [h5, ↓reduceIte] at h
        obtain ⟨k, xs, hx, rfl⟩ := skipPairsUntilBreak_sound n w r h
        refine ⟨_, .indefMap hx, ?_⟩
        have hb : b = 0xBF := UInt8.toNat_inj.mp (by rw [show (0xBF : UInt8).toNat = 191 from rfl]; omega)
        rw [hb]; simp
      simp only [h5, ↓reduceIte] at h
      simp at h
    simp only [h31, ↓reduceIte] at h
    by_cases h7 : b.toNat / 32 = 7
    · simp only [h7, ↓reduceIte] at h
      by_cases h24 : b.toNat % 32 < 24
      · simp only [h24, ↓reduceIte] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨[b], ?_, rfl⟩
        rw [show b = UInt8.ofNat (0xE0 + b.toNat % 32) from eq_ofNat_of_toNat (by omega)]
        exact .simple (by omega)
      simp only [h24, ↓reduceIte] at h
      by_cases h24' : b.toNat % 32 = 24
      · simp only [h24', ↓reduceIte] at h
        rcases w with _ | ⟨v, w⟩
        · simp at h
        · simp only at h
          by_cases hv : 32 ≤ v.toNat
          · simp only [hv, ↓reduceIte] at h
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨[b, v], ?_, rfl⟩
            have hb : b = 0xF8 :=
              UInt8.toNat_inj.mp (by rw [show (0xF8 : UInt8).toNat = 248 from rfl]; omega)
            rw [hb]
            exact .simpleByte hv
          · simp only [hv, ↓reduceIte] at h; simp at h
      simp only [h24', ↓reduceIte] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨a, r1⟩, hra, rfl⟩ := h
      obtain ⟨k, e, hw, hl, rfl⟩ := readArg_split hra h24
      have := argWidth_some hw
      refine ⟨b :: e, ?_, by simp⟩
      rw [show b = UInt8.ofNat (0xE0 + b.toNat % 32) from eq_ofNat_of_toNat (by omega)]
      exact .float hw (by omega) hl
    simp only [h7, ↓reduceIte] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, r1⟩, hra, h⟩ := h
    have hai : b.toNat % 32 < 28 := by
      by_contra hc
      rw [readArg_none (by omega)] at hra
      simp at hra
    obtain ⟨ext, rfl, hh⟩ := head_of_readArg hai hra
    simp only at h
    by_cases h01 : b.toNat / 32 = 0 ∨ b.toNat / 32 = 1
    · simp only [h01, ↓reduceIte] at h
      simp only [Option.some.injEq] at h
      subst h
      rcases h01 with h0 | h1
      · exact ⟨b :: ext, .uint (h0 ▸ hh), rfl⟩
      · exact ⟨b :: ext, .nint (h1 ▸ hh), rfl⟩
    simp only [h01, ↓reduceIte] at h
    by_cases h23 : b.toNat / 32 = 2 ∨ b.toNat / 32 = 3
    · simp only [h23, ↓reduceIte] at h
      by_cases hl : a ≤ r1.length
      · simp only [hl, ↓reduceIte] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨b :: ext ++ r1.take a,
          .string h23 ⟨a, b :: ext, r1.take a, hh, by simp [hl], rfl⟩, ?_⟩
        simp
      · simp only [hl, ↓reduceIte] at h; simp at h
    simp only [h23, ↓reduceIte] at h
    by_cases h4 : b.toNat / 32 = 4
    · simp only [h4, ↓reduceIte] at h
      obtain ⟨xs, hx, rfl⟩ := skipN_sound n a r1 r h
      exact ⟨b :: ext ++ xs, .array (h4 ▸ hh) hx, by simp⟩
    simp only [h4, ↓reduceIte] at h
    by_cases h5 : b.toNat / 32 = 5
    · simp only [h5, ↓reduceIte] at h
      obtain ⟨xs, hx, rfl⟩ := skipN_sound n (2 * a) r1 r h
      exact ⟨b :: ext ++ xs, .map (h5 ▸ hh) hx, by simp⟩
    simp only [h5, ↓reduceIte] at h
    obtain ⟨x, hx, rfl⟩ := skip_sound n r1 r h
    have h6 : b.toNat / 32 = 6 := by omega
    exact ⟨b :: ext ++ x, .tag (h6 ▸ hh) hx, by simp⟩

theorem skipN_sound : ∀ (f k : Nat) (w r : List UInt8), skipN f k w = some r →
    ∃ xs, Items k xs ∧ w = xs ++ r
  | _, 0, w, r, h => by
    simp only [skipN, Option.some.injEq] at h
    exact ⟨[], .nil, by simp [h]⟩
  | 0, _ + 1, _, _, h => by simp [skipN] at h
  | f + 1, k + 1, w, r, h => by
    simp only [skipN, Option.bind_eq_some_iff] at h
    obtain ⟨r1, h1, h2⟩ := h
    obtain ⟨x, hx, rfl⟩ := skip_sound f w r1 h1
    obtain ⟨xs, hxs, rfl⟩ := skipN_sound f k r1 r h2
    exact ⟨x ++ xs, .cons hx hxs, by simp⟩

theorem skipUntilBreak_sound : ∀ (f : Nat) (w r : List UInt8), skipUntilBreak f w = some r →
    ∃ k xs, Items k xs ∧ w = xs ++ breakByte :: r
  | 0, _, _, h => by simp [skipUntilBreak] at h
  | _ + 1, [], _, h => by simp [skipUntilBreak] at h
  | f + 1, b :: w, r, h => by
    simp only [skipUntilBreak] at h
    split_ifs at h with hb
    · simp only [Option.some.injEq] at h
      subst h hb
      exact ⟨0, [], .nil, rfl⟩
    · rw [Option.bind_eq_some_iff] at h
      obtain ⟨r1, h1, h2⟩ := h
      obtain ⟨x, hx, hw⟩ := skip_sound f (b :: w) r1 h1
      obtain ⟨k, xs, hxs, rfl⟩ := skipUntilBreak_sound f r1 r h2
      exact ⟨k + 1, x ++ xs, .cons hx hxs, by simp [hw]⟩

theorem skipPairsUntilBreak_sound : ∀ (f : Nat) (w r : List UInt8),
    skipPairsUntilBreak f w = some r → ∃ k xs, Items (2 * k) xs ∧ w = xs ++ breakByte :: r
  | 0, _, _, h => by simp [skipPairsUntilBreak] at h
  | _ + 1, [], _, h => by simp [skipPairsUntilBreak] at h
  | f + 1, b :: w, r, h => by
    simp only [skipPairsUntilBreak] at h
    split_ifs at h with hb
    · simp only [Option.some.injEq] at h
      subst h hb
      exact ⟨0, [], .nil, rfl⟩
    · rw [Option.bind_eq_some_iff] at h
      obtain ⟨r1, h1, h2⟩ := h
      rw [Option.bind_eq_some_iff] at h2
      obtain ⟨r2, h2, h3⟩ := h2
      obtain ⟨x, hx, hw⟩ := skip_sound f (b :: w) r1 h1
      obtain ⟨y, hy, rfl⟩ := skip_sound f r1 r2 h2
      obtain ⟨k, xs, hxs, rfl⟩ := skipPairsUntilBreak_sound f r2 r h3
      refine ⟨k + 1, x ++ (y ++ xs), ?_, by simp [hw]⟩
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
      exact .cons hx (.cons hy hxs)

end

theorem isWellFormed_iff {w : List UInt8} : isWellFormed w = true ↔ w ∈ wellFormed := by
  unfold isWellFormed
  rw [beq_iff_eq]
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := skip_sound _ w [] h
    rw [List.append_nil]
    exact hx
  · intro h
    simpa using item_skip h (2 * w.length + 1) [] (by omega)

end Silmaril.Proofs.Formats.Cbor.WellFormed

end
