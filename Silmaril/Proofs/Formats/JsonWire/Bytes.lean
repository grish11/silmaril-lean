module

public import Silmaril.Formats.JsonWire.Grammar.Defs
public import Silmaril.Formats.JsonBytes.Thms
public import Silmaril.Formats.Utf8.Thms

/-! # Proofs: the lexemes of the reader against the byte grammar of RFC 8259
(`Silmaril.Formats.JsonWire.Grammar.Thms`)

The character conditions of `Silmaril.Formats.JsonWire.Grammar.Defs` (numbers, string bodies)
are the byte regular expressions of `Silmaril.Formats.JsonBytes` read through UTF-8. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonWire.Bytes

open Silmaril.Formats.JsonWire Silmaril.Formats.JsonWire.Internal
open Silmaril.Formats.JsonBytes Silmaril.Formats.Utf8 RegularExpression

theorem good_digit : Good digit := good_byteRange (by decide)
theorem good_digits : Good digits := good_mul good_digit (good_star good_digit)
theorem good_int : Good int :=
  good_add (good_char (by decide)) (good_mul (good_byteRange (by decide)) (good_star good_digit))
theorem good_frac : Good frac := good_mul (good_char (by decide)) good_digits
theorem good_exp : Good exp :=
  good_mul (good_mul (good_anyOf (by decide)) (good_add good_one (good_anyOf (by decide)))) good_digits
theorem good_number : Good number :=
  good_mul (good_mul (good_mul (good_add good_one (good_char (by decide))) good_int)
    (good_add good_one good_frac)) (good_add good_one good_exp)

theorem flatten_map_singleton (l : List Char) : (l.map ([·])).flatten = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

theorem mem_star_digit {ds : List Char} :
    encode ds ∈ (star digit).matches' ↔ ∀ x ∈ ds, IsDigitChar x := by
  rw [encode_mem_star good_digit]
  constructor
  · rintro ⟨L, rfl, hL⟩ x hx
    obtain ⟨y, hy, hxy⟩ := List.mem_flatten.mp hx
    obtain ⟨c, rfl, h1, h2⟩ := (encode_mem_byteRange (by decide)).mp (hL y hy)
    have hxc : x = c := List.mem_singleton.mp hxy
    subst hxc
    exact ⟨h1, h2⟩
  · intro h
    refine ⟨ds.map ([·]), (flatten_map_singleton ds).symm, ?_⟩
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    exact (encode_mem_byteRange (by decide)).mpr ⟨c, rfl, (h c hc).1, (h c hc).2⟩

theorem mem_digits {ds : List Char} : encode ds ∈ digits.matches' ↔ Digits ds := by
  rw [digits, encode_mem_mul good_digit (good_star good_digit)]
  constructor
  · rintro ⟨c₁, c₂, rfl, h₁, h₂⟩
    obtain ⟨c, rfl, l, u⟩ := (encode_mem_byteRange (by decide)).mp h₁
    refine ⟨by simp, ?_⟩
    intro x hx
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨l, u⟩
    · exact mem_star_digit.mp h₂ x hx
  · rintro ⟨hne, hd⟩
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨[c], cs, rfl, (encode_mem_byteRange (by decide)).mpr ⟨c, rfl, ?_, ?_⟩,
      mem_star_digit.mpr fun x hx => hd x (by simp [hx])⟩
    · exact (hd c (by simp)).1
    · exact (hd c (by simp)).2

theorem ofNat_byte (b : UInt8) (c : Char) (h : c.toNat = b.toNat) (_hc : b < 0x80) :
    Char.ofNat b.toNat = c := by
  rw [← h, Char.ofNat_toNat]

theorem mem_opt_char {b : UInt8} {c : Char} (hb : b < 0x80) (hc : c.toNat = b.toNat) {s : List Char} :
    encode s ∈ (1 + char b).matches' ↔ s = [] ∨ s = [c] := by
  rw [encode_mem_add, encode_mem_one, encode_mem_char hb, ofNat_byte b c hc hb]

theorem mem_int {i : List Char} :
    encode i ∈ int.matches' ↔ i = ['0'] ∨
      ∃ d ds, i = d :: ds ∧ 49 ≤ d.toNat ∧ d.toNat ≤ 57 ∧ ∀ x ∈ ds, IsDigitChar x := by
  rw [int, digit19, encode_mem_add, encode_mem_char (by decide), ofNat_byte 0x30 '0' rfl (by decide),
    encode_mem_mul (good_byteRange (by decide)) (good_star good_digit)]
  constructor
  · rintro (h | ⟨c₁, c₂, rfl, h₁, h₂⟩)
    · exact Or.inl h
    · obtain ⟨d, rfl, l, u⟩ := (encode_mem_byteRange (by decide)).mp h₁
      exact Or.inr ⟨d, c₂, rfl, l, u, mem_star_digit.mp h₂⟩
  · rintro (h | ⟨d, ds, rfl, l, u, hds⟩)
    · exact Or.inl h
    · exact Or.inr ⟨[d], ds, rfl, (encode_mem_byteRange (by decide)).mpr ⟨d, rfl, l, u⟩,
        mem_star_digit.mpr hds⟩

theorem mem_opt_frac {f : List Char} :
    encode f ∈ (1 + frac).matches' ↔ f = [] ∨ ∃ ds, f = '.' :: ds ∧ Digits ds := by
  rw [encode_mem_add, encode_mem_one, frac, encode_mem_mul (good_char (by decide)) good_digits]
  simp only [encode_mem_char (b := 0x2E) (by decide), ofNat_byte 0x2E '.' rfl (by decide)]
  constructor
  · rintro (h | ⟨c₁, c₂, rfl, rfl, h₂⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c₂, rfl, mem_digits.mp h₂⟩
  · rintro (h | ⟨ds, rfl, hds⟩)
    · exact Or.inl h
    · exact Or.inr ⟨['.'], ds, rfl, rfl, mem_digits.mpr hds⟩

theorem mem_opt_exp {e : List Char} :
    encode e ∈ (1 + exp).matches' ↔ e = [] ∨ ∃ x sg ds, e = x :: (sg ++ ds) ∧ (x = 'e' ∨ x = 'E') ∧
      (sg = [] ∨ sg = ['-'] ∨ sg = ['+']) ∧ Digits ds := by
  rw [encode_mem_add, encode_mem_one, exp,
    encode_mem_mul (good_mul (good_anyOf (by decide)) (good_add good_one (good_anyOf (by decide))))
      good_digits]
  simp only [encode_mem_mul (r := anyOf [0x65, 0x45]) (s := 1 + anyOf [0x2D, 0x2B])
    (good_anyOf (by decide)) (good_add good_one (good_anyOf (by decide)))]
  have hE : ∀ {xs : List Char}, encode xs ∈ (anyOf [0x65, 0x45]).matches' ↔ ∃ x, xs = [x] ∧ (x = 'e' ∨ x = 'E') := by
    intro xs
    rw [encode_mem_anyOf (by decide)]
    constructor
    · rintro ⟨b, hb, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact ⟨'e', rfl, Or.inl rfl⟩
      · exact ⟨'E', rfl, Or.inr rfl⟩
    · rintro ⟨x, rfl, rfl | rfl⟩
      · exact ⟨0x65, by simp, rfl⟩
      · exact ⟨0x45, by simp, rfl⟩
  have hS : ∀ {xs : List Char}, encode xs ∈ (1 + anyOf [0x2D, 0x2B]).matches' ↔
      xs = [] ∨ xs = ['-'] ∨ xs = ['+'] := by
    intro xs
    rw [encode_mem_add, encode_mem_one, encode_mem_anyOf (by decide)]
    constructor
    · rintro (h | ⟨b, hb, rfl⟩)
      · exact Or.inl h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    · rintro (h | rfl | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨0x2D, by simp, rfl⟩
      · exact Or.inr ⟨0x2B, by simp, rfl⟩
  constructor
  · rintro (h | ⟨c₁, ds, rfl, ⟨xs, sg, rfl, hx, hsg⟩, hds⟩)
    · exact Or.inl h
    · obtain ⟨x, rfl, hx'⟩ := hE.mp hx
      exact Or.inr ⟨x, sg, ds, by simp, hx', hS.mp hsg, mem_digits.mp hds⟩
  · rintro (h | ⟨x, sg, ds, rfl, hx, hsg, hds⟩)
    · exact Or.inl h
    · exact Or.inr ⟨[x] ++ sg, ds, by simp, ⟨[x], sg, rfl, hE.mpr ⟨x, rfl, hx⟩, hS.mpr hsg⟩,
        mem_digits.mpr hds⟩

/-- **Numbers**: the characters of an RFC 8259 number are the encodings `JsonBytes.number` matches. -/
theorem mem_number {w : List Char} : encode w ∈ number.matches' ↔ NumberChars w := by
  have g1 : Good (1 + char 0x2D) := good_add good_one (good_char (by decide))
  have g2 : Good (1 + frac) := good_add good_one good_frac
  have g3 : Good (1 + exp) := good_add good_one good_exp
  rw [number, encode_mem_mul (good_mul (good_mul g1 good_int) g2) g3]
  constructor
  · rintro ⟨abc, e, rfl, habc, he⟩
    obtain ⟨ab, f, rfl, hab, hf⟩ := (encode_mem_mul (good_mul g1 good_int) g2).mp habc
    obtain ⟨s, i, rfl, hs, hi⟩ := (encode_mem_mul g1 good_int).mp hab
    exact ⟨s, i, f, e, rfl, (mem_opt_char (by decide) rfl).mp hs, mem_int.mp hi, mem_opt_frac.mp hf,
      mem_opt_exp.mp he⟩
  · rintro ⟨s, i, f, e, rfl, hs, hi, hf, he⟩
    exact ⟨s ++ i ++ f, e, rfl, (encode_mem_mul (good_mul g1 good_int) g2).mpr
      ⟨s ++ i, f, rfl, (encode_mem_mul g1 good_int).mpr ⟨s, i, rfl, (mem_opt_char (by decide) rfl).mpr hs,
        mem_int.mpr hi⟩, mem_opt_frac.mpr hf⟩, mem_opt_exp.mpr he⟩

/-! ## Strings -/

theorem good_hexdig : Good hexdig :=
  good_add (good_add good_digit (good_byteRange (by decide))) (good_byteRange (by decide))
theorem good_unescaped : Good unescaped :=
  good_add (good_add (good_add (good_byteRange (by decide)) (good_byteRange (by decide)))
    (good_byteRange (by decide))) good_multibyte
theorem good_shortEscape : Good shortEscape := good_mul (good_char (by decide)) (good_anyOf (by decide))
theorem good_uPrefix : Good uPrefix := good_mul (good_char (by decide)) (good_char (by decide))
theorem good_unitEscape : Good unitEscape :=
  good_mul (good_mul (good_mul (good_mul good_uPrefix good_hexdig) good_hexdig) good_hexdig) good_hexdig
theorem good_strChar : Good (strChar .rfc8259) :=
  good_add (good_add good_unescaped good_shortEscape) good_unitEscape

theorem mem_hexdig {x : List Char} : encode x ∈ hexdig.matches' ↔ ∃ c, x = [c] ∧ IsHexChar c := by
  simp only [hexdig, digit, encode_mem_add, encode_mem_byteRange (lo := 0x30) (hi := 0x39) (by decide),
    encode_mem_byteRange (lo := 0x41) (hi := 0x46) (by decide),
    encode_mem_byteRange (lo := 0x61) (hi := 0x66) (by decide), IsHexChar]
  constructor
  · rintro ((⟨c, rfl, h⟩ | ⟨c, rfl, h⟩) | ⟨c, rfl, h⟩) <;>
      exact ⟨c, rfl, by simp only [UInt8.reduceToNat] at h; omega⟩
  · rintro ⟨c, rfl, h⟩
    rcases h with h | h | h
    · exact Or.inl (Or.inl ⟨c, rfl, by simp only [UInt8.reduceToNat]; omega⟩)
    · exact Or.inr ⟨c, rfl, by simp only [UInt8.reduceToNat]; omega⟩
    · exact Or.inl (Or.inr ⟨c, rfl, by simp only [UInt8.reduceToNat]; omega⟩)

theorem mem_unescaped {x : List Char} :
    encode x ∈ unescaped.matches' ↔ ∃ c, x = [c] ∧ 0x20 ≤ c.toNat ∧ c ≠ '"' ∧ c ≠ '\\' := by
  simp only [unescaped, encode_mem_add, encode_mem_byteRange (lo := 0x20) (hi := 0x21) (by decide),
    encode_mem_byteRange (lo := 0x23) (hi := 0x5B) (by decide),
    encode_mem_byteRange (lo := 0x5D) (hi := 0x7F) (by decide), encode_mem_multibyte]
  have q : ∀ c : Char, c = '"' ↔ c.toNat = 0x22 := fun c =>
    ⟨fun h => by subst h; rfl, fun h => Char.ext (by
      simp only [Char.toNat] at h; exact UInt32.toNat_inj.mp (by simpa using h))⟩
  have bs : ∀ c : Char, c = '\\' ↔ c.toNat = 0x5C := fun c =>
    ⟨fun h => by subst h; rfl, fun h => Char.ext (by
      simp only [Char.toNat] at h; exact UInt32.toNat_inj.mp (by simpa using h))⟩
  constructor
  · rintro (((⟨c, rfl, h⟩ | ⟨c, rfl, h⟩) | ⟨c, rfl, h⟩) | ⟨c, rfl, h⟩) <;>
      refine ⟨c, rfl, ?_, fun e => ?_, fun e => ?_⟩ <;> (try rw [q] at e) <;> (try rw [bs] at e) <;>
      (try simp only [UInt8.reduceToNat] at h) <;> omega
  · rintro ⟨c, rfl, h₁, h₂, h₃⟩
    have h₂ : c.toNat ≠ 0x22 := fun e => h₂ ((q c).mpr e)
    have h₃ : c.toNat ≠ 0x5C := fun e => h₃ ((bs c).mpr e)
    by_cases ha : 0x80 ≤ c.toNat
    · exact Or.inr ⟨c, rfl, ha⟩
    by_cases hb : c.toNat ≤ 0x21
    · exact Or.inl (Or.inl (Or.inl ⟨c, rfl, by simp only [UInt8.reduceToNat]; omega,
        by simp only [UInt8.reduceToNat]; omega⟩))
    by_cases hc : c.toNat ≤ 0x5B
    · exact Or.inl (Or.inl (Or.inr ⟨c, rfl, by simp only [UInt8.reduceToNat]; omega,
        by simp only [UInt8.reduceToNat]; omega⟩))
    · exact Or.inl (Or.inr ⟨c, rfl, by simp only [UInt8.reduceToNat]; omega,
        by simp only [UInt8.reduceToNat]; omega⟩)

theorem mem_shortEscape {x : List Char} :
    encode x ∈ shortEscape.matches' ↔ ∃ e, x = ['\\', e] ∧ e ∈ ['"', '\\', '/', 'b', 'f', 'n', 'r', 't'] := by
  rw [shortEscape, encode_mem_mul (good_char (by decide)) (good_anyOf (by decide))]
  simp only [encode_mem_char (b := 0x5C) (by decide), encode_mem_anyOf (l := [0x22, 0x5C, 0x2F, 0x62, 0x66, 0x6E, 0x72, 0x74]) (by decide)]
  constructor
  · rintro ⟨_, _, rfl, rfl, b, hb, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    exact ⟨Char.ofNat b.toNat, rfl, by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide⟩
  · rintro ⟨e, rfl, he⟩
    refine ⟨['\\'], [e], rfl, rfl, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0x22, by simp, rfl⟩
    · exact ⟨0x5C, by simp, rfl⟩
    · exact ⟨0x2F, by simp, rfl⟩
    · exact ⟨0x62, by simp, rfl⟩
    · exact ⟨0x66, by simp, rfl⟩
    · exact ⟨0x6E, by simp, rfl⟩
    · exact ⟨0x72, by simp, rfl⟩
    · exact ⟨0x74, by simp, rfl⟩

theorem mem_unitEscape {x : List Char} :
    encode x ∈ unitEscape.matches' ↔ ∃ a b c d, x = ['\\', 'u', a, b, c, d] ∧
      IsHexChar a ∧ IsHexChar b ∧ IsHexChar c ∧ IsHexChar d := by
  have g1 := good_mul good_uPrefix good_hexdig
  have g2 := good_mul g1 good_hexdig
  have g3 := good_mul g2 good_hexdig
  have hu : ∀ x : List Char, encode x ∈ uPrefix.matches' ↔ x = ['\\', 'u'] := by
    intro x
    rw [uPrefix, encode_mem_mul (good_char (by decide)) (good_char (by decide))]
    simp only [encode_mem_char (b := 0x5C) (by decide), encode_mem_char (b := 0x75) (by decide)]
    constructor
    · rintro ⟨_, _, rfl, rfl, rfl⟩; rfl
    · rintro rfl; exact ⟨_, _, rfl, rfl, rfl⟩
  rw [unitEscape, encode_mem_mul g3 good_hexdig]
  simp only [encode_mem_mul g2 good_hexdig, encode_mem_mul g1 good_hexdig,
    encode_mem_mul good_uPrefix good_hexdig, hu, mem_hexdig]
  constructor
  · rintro ⟨_, _, rfl, ⟨_, _, rfl, ⟨_, _, rfl, ⟨_, _, rfl, rfl, ⟨a, rfl, ha⟩⟩,
      ⟨b, rfl, hb⟩⟩, ⟨c, rfl, hc⟩⟩, ⟨d, rfl, hd⟩⟩
    exact ⟨a, b, c, d, rfl, ha, hb, hc, hd⟩
  · rintro ⟨a, b, c, d, rfl, ha, hb, hc, hd⟩
    exact ⟨_, [d], rfl, ⟨_, [c], rfl, ⟨_, [b], rfl, ⟨['\\', 'u'], [a], rfl, rfl,
      ⟨a, rfl, ha⟩⟩, ⟨b, rfl, hb⟩⟩, ⟨c, rfl, hc⟩⟩, ⟨d, rfl, hd⟩⟩

/-- One `char` of an RFC 8259 string. -/
def StrPiece (x : List Char) : Prop :=
  (∃ c, x = [c] ∧ 0x20 ≤ c.toNat ∧ c ≠ '"' ∧ c ≠ '\\') ∨
  (∃ e, x = ['\\', e] ∧ e ∈ ['"', '\\', '/', 'b', 'f', 'n', 'r', 't']) ∨
  (∃ a b c d, x = ['\\', 'u', a, b, c, d] ∧ IsHexChar a ∧ IsHexChar b ∧ IsHexChar c ∧ IsHexChar d)

theorem mem_strChar {x : List Char} : encode x ∈ (strChar .rfc8259).matches' ↔ StrPiece x := by
  rw [strChar, encode_mem_add, encode_mem_add, mem_unescaped, mem_shortEscape, mem_unitEscape, StrPiece,
    or_assoc]

theorem strBody_iff {b : List Char} :
    StrBody b ↔ ∃ L : List (List Char), b = L.flatten ∧ ∀ x ∈ L, StrPiece x := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], rfl, by simp⟩
    | @plain c _ h₁ h₂ h₃ _ ih =>
      obtain ⟨L, rfl, hL⟩ := ih
      refine ⟨[c] :: L, by simp, fun x hx => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl ⟨c, rfl, h₁, h₂, h₃⟩
      · exact hL x hx
    | @escape e _ he _ ih =>
      obtain ⟨L, rfl, hL⟩ := ih
      refine ⟨['\\', e] :: L, by simp, fun x hx => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr (Or.inl ⟨e, rfl, he⟩)
      · exact hL x hx
    | @unit a b' c d _ ha hb hc hd _ ih =>
      obtain ⟨L, rfl, hL⟩ := ih
      refine ⟨['\\', 'u', a, b', c, d] :: L, by simp, fun x hx => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr (Or.inr ⟨a, b', c, d, rfl, ha, hb, hc, hd⟩)
      · exact hL x hx
  · rintro ⟨L, rfl, hL⟩
    induction L with
    | nil => exact .nil
    | cons x L ih =>
      have ih := ih fun y hy => hL y (by simp [hy])
      rcases hL x (by simp) with ⟨c, rfl, h₁, h₂, h₃⟩ | ⟨e, rfl, he⟩ |
          ⟨a, b', c, d, rfl, ha, hb, hc, hd⟩
      · exact .plain h₁ h₂ h₃ ih
      · exact .escape he ih
      · exact .unit ha hb hc hd ih

theorem mem_strBody {b : List Char} : encode b ∈ (star (strChar .rfc8259)).matches' ↔ StrBody b := by
  rw [encode_mem_star good_strChar, strBody_iff]
  simp only [mem_strChar]

/-- **Strings**: the characters of an RFC 8259 string are the encodings `JsonBytes.string` matches. -/
theorem mem_string {w : List Char} :
    encode w ∈ (string .rfc8259).matches' ↔ ∃ b, w = '"' :: (b ++ ['"']) ∧ StrBody b := by
  have g := good_mul (good_char (b := 0x22) (by decide)) (good_star good_strChar)
  rw [string, encode_mem_mul g (good_char (b := 0x22) (by decide))]
  simp only [encode_mem_mul (r := char 0x22) (s := star (strChar .rfc8259)) (good_char (by decide))
    (good_star good_strChar), encode_mem_char (b := 0x22) (by decide), mem_strBody]
  constructor
  · rintro ⟨_, _, rfl, ⟨_, b, rfl, rfl, hb⟩, rfl⟩
    exact ⟨b, rfl, hb⟩
  · rintro ⟨b, rfl, hb⟩
    exact ⟨'"' :: b, ['"'], by simp, ⟨['"'], b, rfl, rfl, hb⟩, rfl⟩

end Silmaril.Proofs.Formats.JsonWire.Bytes

end
