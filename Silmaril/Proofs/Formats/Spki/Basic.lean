module

public import Silmaril.Formats.Spki.Defs

/-! # Proofs: SPKI S-expressions in canonical form (`Silmaril.Formats.Spki.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Spki

open Silmaril.Formats.Spki

/-! ## Decimal numerals -/

theorem foldl_ge (t : List UInt8) (a : Nat) :
    a ≤ t.foldl (fun n d => 10 * n + (d.toNat - 0x30)) a := by
  induction t generalizing a with
  | nil => exact le_rfl
  | cons d t ih =>
    simp only [List.foldl_cons]
    exact le_trans (by omega : a ≤ 10 * a + (d.toNat - 0x30)) (ih _)

theorem digitsValue_append (l : List UInt8) (d : UInt8) :
    digitsValue (l ++ [d]) = 10 * digitsValue l + (d.toNat - 0x30) := by
  simp [digitsValue, List.foldl_append]

theorem digitsValue_cons_pos {d : UInt8} {t : List UInt8} (h : 0x31 ≤ d) :
    1 ≤ digitsValue (d :: t) := by
  have := foldl_ge t (10 * 0 + (d.toNat - 0x30))
  rw [UInt8.le_iff_toNat_le] at h
  simp only [digitsValue, List.foldl_cons] at this ⊢
  simp at h
  omega

theorem decimal_lt {n : Nat} (h : n < 10) : decimal n = [UInt8.ofNat (0x30 + n)] := by
  rw [decimal, ite_eq_left_of_eq_true _ _ (eq_true h)]

theorem decimal_ge {n : Nat} (h : ¬ n < 10) :
    decimal n = decimal (n / 10) ++ [UInt8.ofNat (0x30 + n % 10)] := by
  rw [decimal, ite_eq_right_of_eq_false _ _ (eq_false h)]

theorem isDigit_ofNat {k : Nat} (h : k < 10) : isDigit (UInt8.ofNat (0x30 + k)) = true := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
    UInt8.toNat_ofNat']
  simp
  omega

theorem toNat_ofNat_digit {k : Nat} (h : k < 10) : (UInt8.ofNat (0x30 + k)).toNat - 0x30 = k := by
  simp only [UInt8.toNat_ofNat']
  omega

theorem decimal_digits (n : Nat) : ∀ b ∈ decimal n, isDigit b = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · rw [decimal_lt h]; intro b hb; rw [List.mem_singleton] at hb; subst hb; exact isDigit_ofNat h
    · rw [decimal_ge h]
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ih _ (by omega) b hb
      · rw [List.mem_singleton] at hb; subst hb; exact isDigit_ofNat (Nat.mod_lt _ (by omega))

theorem digitsValue_decimal (n : Nat) : digitsValue (decimal n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · rw [decimal_lt h]; simp only [digitsValue, List.foldl_cons, List.foldl_nil]
      rw [toNat_ofNat_digit h]; omega
    · rw [decimal_ge h, digitsValue_append, ih _ (by omega),
        toNat_ofNat_digit (Nat.mod_lt _ (by omega))]
      omega

theorem decimal_ne_nil (n : Nat) : decimal n ≠ [] := by
  by_cases h : n < 10
  · rw [decimal_lt h]; simp
  · rw [decimal_ge h]; simp

theorem isDecimal_decimal (n : Nat) : IsDecimal (decimal n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · rw [decimal_lt h]
      by_cases h0 : n = 0
      · subst h0; exact Or.inl rfl
      · refine Or.inr ⟨_, [], rfl, ?_, ?_, by simp⟩ <;>
        · rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat']; simp; omega
    · rw [decimal_ge h]
      have hm : 1 ≤ n / 10 := by omega
      rcases ih (n / 10) (by omega) with h1 | ⟨d, t, h1, hd1, hd2, ht⟩
      · have := digitsValue_decimal (n / 10)
        rw [h1] at this
        simp [digitsValue] at this
        omega
      · rw [h1]
        refine Or.inr ⟨d, t ++ [UInt8.ofNat (0x30 + n % 10)], by simp, hd1, hd2, ?_⟩
        intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact ht b hb
        · rw [List.mem_singleton] at hb; subst hb; exact isDigit_ofNat (Nat.mod_lt _ (by omega))

theorem ofNat_toNat_digit {d : UInt8} (h : isDigit d = true) :
    UInt8.ofNat (0x30 + (d.toNat - 0x30)) = d := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at h
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_ofNat']
  simp at h
  omega

theorem decimal_digitsValue_cons {d : UInt8} {t : List UInt8} (hd : 0x31 ≤ d) (hd' : d ≤ 0x39)
    (ht : ∀ b ∈ t, isDigit b = true) : decimal (digitsValue (d :: t)) = d :: t := by
  induction t using List.reverseRecOn with
  | nil =>
    have hdig : isDigit d = true := by
      simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨UInt8.le_trans (by decide) hd, hd'⟩
    have h10 : d.toNat - 0x30 < 10 := by
      rw [UInt8.le_iff_toNat_le] at hd'; simp at hd'; omega
    simp only [digitsValue, List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add]
    rw [decimal_lt h10, ofNat_toNat_digit hdig]
  | append_singleton t e ih =>
    have he : isDigit e = true := ht e (by simp)
    have ih' := ih (fun b hb => ht b (by simp [hb]))
    have hpos := digitsValue_cons_pos (t := t) hd
    have he10 : e.toNat - 0x30 < 10 := by
      simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at he
      simp at he; omega
    rw [← List.cons_append, digitsValue_append, decimal_ge (by omega)]
    have h1 : (10 * digitsValue (d :: t) + (e.toNat - 0x30)) / 10 = digitsValue (d :: t) := by
      omega
    have h2 : (10 * digitsValue (d :: t) + (e.toNat - 0x30)) % 10 = e.toNat - 0x30 := by omega
    rw [h1, h2, ih', ofNat_toNat_digit he]

theorem decimal_digitsValue {ds : List UInt8} (h : IsDecimal ds) : decimal (digitsValue ds) = ds := by
  rcases h with rfl | ⟨d, t, rfl, hd, hd', ht⟩
  · rw [show digitsValue [0x30] = 0 from rfl, decimal_lt (by omega)]; rfl
  · exact decimal_digitsValue_cons hd hd' ht

theorem isDecimal_iff {ds : List UInt8} : IsDecimal ds ↔ ∃ n, ds = decimal n :=
  ⟨fun h => ⟨_, (decimal_digitsValue h).symm⟩, fun ⟨n, h⟩ => h ▸ isDecimal_decimal n⟩

/-! ## Reading numerals and verbatim strings -/

theorem takeWhile_append_of_all {l r : List UInt8} {q : UInt8 → Bool} (hl : ∀ x ∈ l, q x = true) :
    (l ++ r).takeWhile q = l ++ r.takeWhile q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.cons_append, List.takeWhile_cons_of_pos (hl a (by simp)),
      ih (fun x hx => hl x (by simp [hx])), List.cons_append]

theorem dropWhile_append_of_all {l r : List UInt8} {q : UInt8 → Bool} (hl : ∀ x ∈ l, q x = true) :
    (l ++ r).dropWhile q = r.dropWhile q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.cons_append, List.dropWhile_cons_of_pos (hl a (by simp)),
      ih (fun x hx => hl x (by simp [hx]))]

theorem readDecimal_decimal (n : Nat) (r : List UInt8) :
    readDecimal (decimal n ++ 0x3A :: r) = some (n, r) := by
  have hc : isDigit 0x3A = false := by decide
  have h1 := takeWhile_append_of_all (r := 0x3A :: r) (decimal_digits n)
  have h2 := dropWhile_append_of_all (r := 0x3A :: r) (decimal_digits n)
  rw [List.takeWhile_cons_of_neg (by simp [hc]), List.append_nil] at h1
  rw [List.dropWhile_cons_of_neg (by simp [hc])] at h2
  simp [readDecimal, h1, h2, digitsValue_decimal]

theorem eq_of_readDecimal {w r : List UInt8} {n : Nat} (h : readDecimal w = some (n, r)) :
    w = decimal n ++ 0x3A :: r := by
  have hw := List.takeWhile_append_dropWhile (p := isDigit) (l := w)
  unfold readDecimal at h
  cases hd : w.dropWhile isDigit with
  | nil => simp [hd] at h
  | cons b r' =>
    simp only [hd] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    nth_rewrite 1 [← hw]
    rw [hd, hc.1, hc.2]

theorem readVerbatim_verbatim (s r : List UInt8) :
    readVerbatim (verbatim s ++ r) = some (s, r) := by
  simp [readVerbatim, verbatim, readDecimal_decimal]

theorem eq_of_readVerbatim {w s r : List UInt8} (h : readVerbatim w = some (s, r)) :
    w = verbatim s ++ r := by
  unfold readVerbatim at h
  cases hd : readDecimal w with
  | none => simp [hd] at h
  | some nr =>
    obtain ⟨n, r'⟩ := nr
    simp only [hd] at h
    split_ifs at h with hn
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [eq_of_readDecimal hd, verbatim, List.length_take, Nat.min_eq_left hn,
      List.append_assoc, List.cons_append, List.take_append_drop]

theorem readHinted_hinted (h s r : List UInt8) :
    readHinted (verbatim h ++ 0x5D :: verbatim s ++ r) = some (.atom (some h) s, r) := by
  simp [readHinted, List.append_assoc, readVerbatim_verbatim]

theorem eq_of_readHinted {w r : List UInt8} {x : Sexp} (h : readHinted w = some (x, r)) :
    0x5B :: w = encode x ++ r := by
  unfold readHinted at h
  cases hv : readVerbatim w with
  | none => simp [hv] at h
  | some hr =>
    obtain ⟨hh, r'⟩ := hr
    cases r' with
    | nil => simp [hv] at h
    | cons b r' =>
      simp only [hv] at h
      split_ifs at h with hb
      obtain ⟨⟨s, r''⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [eq_of_readVerbatim hv, hb, eq_of_readVerbatim hs]
      simp [encode]

/-! ## Shapes of encodings -/

theorem verbatim_head (s r : List UInt8) :
    ∃ d w, verbatim s ++ r = d :: w ∧ isDigit d = true := by
  obtain ⟨d, t, ht⟩ := List.exists_cons_of_ne_nil (decimal_ne_nil s.length)
  refine ⟨d, t ++ 0x3A :: s ++ r, ?_, decimal_digits _ d (by rw [ht]; exact List.mem_cons_self)⟩
  rw [verbatim, ht]
  simp

theorem verbatim_length (s : List UInt8) : 2 ≤ (verbatim s).length := by
  have := List.length_pos_iff.mpr (decimal_ne_nil s.length)
  simp only [verbatim, List.length_append, List.length_cons]
  omega

theorem encode_length (x : Sexp) : 2 ≤ (encode x).length := by
  cases x with
  | atom h s =>
    cases h with
    | none => exact verbatim_length s
    | some h =>
      have := verbatim_length s
      simp only [encode, List.length_cons, List.length_append]
      omega
  | list xs => simp only [encode, List.length_cons, List.length_append]; omega

/-- The first byte of an encoding is `(`, `[` or a digit, never `)`. -/
theorem encode_head (x : Sexp) (r : List UInt8) :
    ∃ b w, encode x ++ r = b :: w ∧ b ≠ 0x29 := by
  cases x with
  | atom h s =>
    cases h with
    | none =>
      obtain ⟨d, w, hw, hd⟩ := verbatim_head s r
      exact ⟨d, w, hw, by rintro rfl; exact absurd hd (by decide)⟩
    | some h => exact ⟨0x5B, verbatim h ++ 0x5D :: verbatim s ++ r, by simp [encode], by decide⟩
  | list xs => exact ⟨0x28, encodeList xs ++ 0x29 :: r, by simp [encode], by decide⟩

/-! ## The parser inverts the encoding -/

theorem parse_verbatim {n : Nat} (s r : List UInt8) :
    parse (n + 1) (verbatim s ++ r) = some (.atom none s, r) := by
  obtain ⟨d, w, hw, hd⟩ := verbatim_head s r
  have hrv := readVerbatim_verbatim s r
  rw [hw] at hrv ⊢
  have h28 : d ≠ 0x28 := by rintro rfl; exact absurd hd (by decide)
  have h5B : d ≠ 0x5B := by rintro rfl; exact absurd hd (by decide)
  simp [parse, h28, h5B, hrv]

mutual

theorem parse_encode : ∀ (x : Sexp) (n : Nat) (rest : List UInt8),
    (encode x).length < n → parse n (encode x ++ rest) = some (x, rest)
  | .atom none s, n, rest, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact parse_verbatim s rest
  | .atom (some h) s, n, rest, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := readHinted_hinted h s rest
    simp only [List.append_assoc, List.cons_append] at this
    simp [encode, parse, this]
  | .list xs, n, rest, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [encode, List.length_cons, List.length_append] at hn
    have := parseList_encode xs k rest (by simp at hn; omega)
    simp [encode, parse, this]

theorem parseList_encode : ∀ (xs : List Sexp) (n : Nat) (rest : List UInt8),
    (encodeList xs).length + 1 < n → parseList n (encodeList xs ++ 0x29 :: rest) = some (xs, rest)
  | [], n, rest, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [encodeList, parseList]
  | x :: xs, n, rest, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hx := encode_length x
    simp only [encodeList, List.length_append] at hn
    have hp := parse_encode x k (encodeList xs ++ 0x29 :: rest) (by omega)
    have hl := parseList_encode xs k rest (by omega)
    obtain ⟨b, w, hw, hb⟩ := encode_head x (encodeList xs ++ 0x29 :: rest)
    rw [hw] at hp
    simp only [encodeList, List.append_assoc, hw, parseList, hb, ite_false, hp, hl,
      Option.map_some]

end

mutual

theorem eq_of_parse : ∀ {n : Nat} {w r : List UInt8} {x : Sexp},
    parse n w = some (x, r) → w = encode x ++ r
  | 0, _, _, _, h => by simp [parse] at h
  | _ + 1, [], _, _, h => by simp [parse] at h
  | n + 1, b :: w, r, x, h => by
    simp only [parse] at h
    split_ifs at h with h28 h5B
    · subst h28
      obtain ⟨⟨xs, r'⟩, hl, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [eq_of_parseList hl]
      simp [encode]
    · subst h5B
      exact eq_of_readHinted h
    · obtain ⟨⟨s, r'⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [eq_of_readVerbatim hs]
      rfl

theorem eq_of_parseList : ∀ {n : Nat} {w r : List UInt8} {xs : List Sexp},
    parseList n w = some (xs, r) → w = encodeList xs ++ 0x29 :: r
  | 0, _, _, _, h => by simp [parseList] at h
  | _ + 1, [], _, _, h => by simp [parseList] at h
  | n + 1, b :: w, r, xs, h => by
    simp only [parseList] at h
    split_ifs at h with h29
    · subst h29
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · cases hp : parse n (b :: w) with
      | none => simp [hp] at h
      | some xr =>
        obtain ⟨x, r'⟩ := xr
        simp only [hp] at h
        obtain ⟨⟨ys, r''⟩, hl, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [eq_of_parse hp, eq_of_parseList hl]
        simp [encodeList]

end

theorem decode_eq_some_iff {w : List UInt8} {x : Sexp} : decode w = some x ↔ w = encode x := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · rename_i y hp
      simp only [Option.some.injEq] at h
      subst h
      simpa using eq_of_parse hp
    · simp at h
  · rintro rfl
    have := parse_encode x ((encode x).length + 1) [] (by omega)
    rw [List.append_nil] at this
    simp [decode, this]

theorem encode_injective : Function.Injective encode := fun x y h => by
  have hx := decode_eq_some_iff.mpr (rfl : encode x = encode x)
  rw [h, decode_eq_some_iff.mpr rfl] at hx
  exact (Option.some.inj hx).symm

/-! ## The ABNF -/

theorem isVerbatim_iff {w : List UInt8} : IsVerbatim w ↔ ∃ s, w = verbatim s := by
  constructor
  · rintro ⟨ds, s, hd, hv, rfl⟩
    refine ⟨s, ?_⟩
    rw [verbatim, ← hv, decimal_digitsValue hd]
  · rintro ⟨s, rfl⟩
    exact ⟨_, s, isDecimal_decimal _, digitsValue_decimal _, rfl⟩

theorem encodeList_eq_flatten (xs : List Sexp) : encodeList xs = (xs.map encode).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeList, ih]

mutual

theorem abnf_encode : ∀ x : Sexp, ABNF (encode x)
  | .atom none s => .string (Or.inl (isVerbatim_iff.mpr ⟨s, rfl⟩))
  | .atom (some h) s =>
    .string (Or.inr ⟨_, _, isVerbatim_iff.mpr ⟨h, rfl⟩, isVerbatim_iff.mpr ⟨s, rfl⟩, rfl⟩)
  | .list xs => by
    rw [encode, encodeList_eq_flatten]
    exact .list (abnf_encodeList xs)

theorem abnf_encodeList : ∀ xs : List Sexp, ∀ w ∈ xs.map encode, ABNF w
  | [], _, h => by simp at h
  | x :: xs, w, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact abnf_encode x
    · exact abnf_encodeList xs w h

end

theorem exists_encode_of_abnf {w : List UInt8} (h : ABNF w) : ∃ x, w = encode x := by
  induction h with
  | string hs =>
    rcases hs with hv | ⟨hb, v, hh, hv, rfl⟩
    · obtain ⟨s, rfl⟩ := isVerbatim_iff.mp hv
      exact ⟨.atom none s, rfl⟩
    · obtain ⟨h, rfl⟩ := isVerbatim_iff.mp hh
      obtain ⟨s, rfl⟩ := isVerbatim_iff.mp hv
      exact ⟨.atom (some h) s, rfl⟩
  | @list xs _ ih =>
    have : ∃ ys : List Sexp, xs = ys.map encode := by
      clear * - ih
      induction xs with
      | nil => exact ⟨[], rfl⟩
      | cons x xs ihx =>
        obtain ⟨y, rfl⟩ := ih x (by simp)
        obtain ⟨ys, rfl⟩ := ihx (fun z hz => ih z (by simp [hz]))
        exact ⟨y :: ys, rfl⟩
    obtain ⟨ys, rfl⟩ := this
    exact ⟨.list ys, by rw [encode, encodeList_eq_flatten]⟩

theorem mem_canonical_iff {w : List UInt8} : w ∈ canonical ↔ ABNF w := by
  constructor
  · rintro ⟨x, rfl⟩; exact abnf_encode x
  · intro h; obtain ⟨x, rfl⟩ := exists_encode_of_abnf h; exact ⟨x, rfl⟩

end Silmaril.Proofs.Formats.Spki

end
