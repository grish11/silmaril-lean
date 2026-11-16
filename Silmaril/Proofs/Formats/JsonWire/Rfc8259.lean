module

public import Silmaril.Proofs.Formats.JsonWire.Parser
public import Silmaril.Proofs.Formats.JsonWire.Lexer
public import Silmaril.Proofs.Formats.JsonWire.Bytes
public import Silmaril.Formats.JsonWire.Defs

/-! # Proofs: the RFC 8259 reader accepts exactly the JSON texts (`Silmaril.Formats.JsonWire.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonWire.Rfc8259

open Silmaril.Formats.JsonWire Silmaril.Formats.JsonWire.Internal
open Silmaril.Formats.JsonBytes Silmaril.Formats.Utf8 RegularExpression
open Silmaril.Proofs.Formats.JsonWire.Lexer Silmaril.Proofs.Formats.JsonWire.Bytes

/-- All whitespace. -/
def W (cs : List Char) : Prop := ∀ c ∈ cs, white .rfc8259 c = true

theorem W_nil : W [] := by simp [W]
theorem W_append {a b : List Char} (ha : W a) (hb : W b) : W (a ++ b) := by
  intro c hc; simp only [List.mem_append] at hc; rcases hc with hc | hc; exacts [ha c hc, hb c hc]

theorem good_ws : Good ws := good_star (good_anyOf (by decide))

theorem mem_ws_chars {cs : List Char} : encode cs ∈ ws.matches' ↔ W cs := by
  rw [ws, wsByte, encode_mem_star (good_anyOf (by decide))]
  simp only [encode_mem_anyOf (l := [0x20, 0x09, 0x0A, 0x0D]) (by decide)]
  constructor
  · rintro ⟨L, rfl, hL⟩ c hc
    obtain ⟨y, hy, hcy⟩ := List.mem_flatten.mp hc
    obtain ⟨b, hb, rfl⟩ := hL y hy
    have : c = Char.ofNat b.toNat := List.mem_singleton.mp hcy
    subst this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> rfl
  · intro h
    refine ⟨cs.map ([·]), (flatten_map_singleton cs).symm, ?_⟩
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    have := (white_rfc c).mp (h c hc)
    rcases this with rfl | rfl | rfl | rfl
    · exact ⟨0x20, by simp, rfl⟩
    · exact ⟨0x09, by simp, rfl⟩
    · exact ⟨0x0D, by simp, rfl⟩
    · exact ⟨0x0A, by simp, rfl⟩

theorem good_structural {b : UInt8} (h : b < 0x80) : Good (structural b) :=
  good_mul (good_mul good_ws (good_char h)) good_ws

theorem mem_structural {b : UInt8} {c : Char} (hb : b < 0x80) (hc : c.toNat = b.toNat) {cs : List Char} :
    encode cs ∈ (structural b).matches' ↔ ∃ a a', cs = a ++ [c] ++ a' ∧ W a ∧ W a' := by
  rw [structural, encode_mem_mul (good_mul good_ws (good_char hb)) good_ws]
  simp only [encode_mem_mul (r := ws) (s := char b) good_ws (good_char hb), encode_mem_char hb,
    ofNat_byte b c hc hb, mem_ws_chars]
  constructor
  · rintro ⟨_, a', rfl, ⟨a, _, rfl, ha, rfl⟩, ha'⟩
    exact ⟨a, a', rfl, ha, ha'⟩
  · rintro ⟨a, a', rfl, ha, ha'⟩
    exact ⟨a ++ [c], a', rfl, ⟨a, [c], rfl, ha, rfl⟩, ha'⟩

theorem mem_word_chars {l : List UInt8} (h : ∀ b ∈ l, b < 0x80) {cs : List Char} :
    encode cs ∈ (word l).matches' ↔ cs = ofAscii l := by
  rw [mem_word]
  constructor
  · intro e; exact eq_ofAscii e h
  · rintro rfl; exact encode_ofAscii h

theorem good_string : Good (string .rfc8259) :=
  good_mul (good_mul (good_char (b := 0x22) (by decide)) (good_star good_strChar)) (good_char (by decide))

/-- **Scalars**: the literals, numbers and strings. -/
theorem mem_scalar {cs : List Char} : encode cs ∈ (Silmaril.Formats.JsonBytes.scalar .rfc8259).matches' ↔
    cs = "false".toList ∨ cs = "null".toList ∨ cs = "true".toList ∨ NumberChars cs ∨
      ∃ b, cs = '"' :: (b ++ ['"']) ∧ StrBody b := by
  rw [Silmaril.Formats.JsonBytes.scalar, encode_mem_add, encode_mem_add, encode_mem_add, encode_mem_add,
    falseLit, nullLit, trueLit,
    mem_word_chars (by decide), mem_word_chars (by decide), mem_word_chars (by decide), mem_number,
    mem_string]
  simp only [or_assoc]
  rfl

/-! ## Lexed token sequences -/

theorem lexes_nil {cs : List Char} (h : Lexes cs []) : W cs := by
  generalize hts : ([] : List Token) = ts at h
  induction h with
  | nil => exact W_nil
  | white hc _ ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact ih hts x hx
  | token _ _ _ => simp at hts

theorem lexes_cons {cs : List Char} {t : Token} {ts : List Token} (h : Lexes cs (t :: ts)) :
    ∃ a l r, cs = a ++ l ++ r ∧ W a ∧ Lexeme l t ∧ Lexes r ts := by
  generalize hts : t :: ts = ts' at h
  induction h with
  | nil => simp at hts
  | @white c cs ts' hc _ ih =>
    obtain ⟨a, l, r, he, ha, hl, hr⟩ := ih hts
    refine ⟨c :: a, l, r, by simp [he], fun x hx => ?_, hl, hr⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact ha x hx
  | @token l cs t' ts' hl hr _ =>
    simp only [List.cons.injEq] at hts
    obtain ⟨rfl, rfl⟩ := hts
    exact ⟨[], l, cs, by simp, W_nil, hl, hr⟩

theorem lexes_append {cs : List Char} {ts₁ ts₂ : List Token} (h : Lexes cs (ts₁ ++ ts₂)) :
    ∃ c₁ c₂, cs = c₁ ++ c₂ ∧ Lexes c₁ ts₁ ∧ Lexes c₂ ts₂ := by
  induction ts₁ generalizing cs with
  | nil => exact ⟨[], cs, rfl, .nil, h⟩
  | cons t ts ih =>
    obtain ⟨a, l, r, rfl, ha, hl, hr⟩ := lexes_cons h
    obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := ih hr
    exact ⟨a ++ l ++ c₁, c₂, by simp, by simpa using lexes_white_append ha (.token hl h₁), h₂⟩

theorem lexes_single {cs : List Char} {t : Token} (h : Lexes cs [t]) :
    ∃ a l b, cs = a ++ l ++ b ∧ W a ∧ W b ∧ Lexeme l t := by
  obtain ⟨a, l, r, rfl, ha, hl, hr⟩ := lexes_cons h
  exact ⟨a, l, r, rfl, ha, lexes_nil hr, hl⟩

theorem lexeme_punct {l : List Char} {t : Token} {c : Char} (h : Lexeme l t)
    (ht : t = .arrayOpen ∧ c = '[' ∨ t = .arrayClose ∧ c = ']' ∨ t = .objectOpen ∧ c = '{' ∨
      t = .objectClose ∧ c = '}' ∨ t = .comma ∧ c = ',' ∨ t = .colon ∧ c = ':') : l = [c] := by
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases h <;> rfl

/-- A punctuation token with the whitespace around it: one structural token of the grammar. -/
theorem lexes_punct {cs : List Char} {t : Token} {c : Char} (h : Lexes cs [t])
    (ht : t = .arrayOpen ∧ c = '[' ∨ t = .arrayClose ∧ c = ']' ∨ t = .objectOpen ∧ c = '{' ∨
      t = .objectClose ∧ c = '}' ∨ t = .comma ∧ c = ',' ∨ t = .colon ∧ c = ':') :
    ∃ a a', cs = a ++ [c] ++ a' ∧ W a ∧ W a' := by
  obtain ⟨a, l, a', rfl, ha, ha', hl⟩ := lexes_single h
  rw [lexeme_punct hl ht]
  exact ⟨a, a', rfl, ha, ha'⟩

theorem lexeme_scalar {l : List Char} {t : Token} (h : Lexeme l t) (ht : t.IsScalar) :
    encode l ∈ (Silmaril.Formats.JsonBytes.scalar .rfc8259).matches' := by
  rw [mem_scalar]
  cases h with
  | string hb => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl, hb⟩)))
  | number hw => exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
  | true_ => exact Or.inr (Or.inr (Or.inl rfl))
  | false_ => exact Or.inl rfl
  | null => exact Or.inr (Or.inl rfl)
  | _ => simp [Token.IsScalar] at ht

theorem lexeme_string {l : List Char} {k : Units} (h : Lexeme l (.string k)) :
    encode l ∈ (string .rfc8259).matches' := by
  cases h with
  | string hb => exact mem_string.mpr ⟨_, rfl, hb⟩

theorem mem_structural' {b : UInt8} {c : Char} (hb : b < 0x80) (hc : c.toNat = b.toNat)
    {a a' : List Char} (ha : W a) (ha' : W a') : encode (a ++ [c] ++ a') ∈ (structural b).matches' :=
  (mem_structural hb hc).mpr ⟨a, a', rfl, ha, ha'⟩

/-! ## The reader's tokens make a JSON text (soundness) -/

mutual

theorem value_of_lexes {ts : List Token} : TValue ts → ∀ {cs : List Char}, Lexes cs ts →
    ∃ a v b, cs = a ++ v ++ b ∧ W a ∧ W b ∧ Value .rfc8259 (encode v)
  | .scalar ht, cs, h => by
    obtain ⟨a, l, b, rfl, ha, hb, hl⟩ := lexes_single h
    exact ⟨a, l, b, rfl, ha, hb, .scalar (lexeme_scalar hl ht)⟩
  | .array (xs := xs) hx, cs, h => by
    obtain ⟨a, l, r, rfl, ha, hl, hr⟩ := lexes_cons h
    have hl' : l = ['['] := lexeme_punct hl (Or.inl ⟨rfl, rfl⟩)
    subst hl'
    rcases elems_of_lexes hx hr with he | ⟨a₁, ys, e, rfl, ha₁, hys, he⟩
    · refine ⟨a, ['['] ++ r, [], by simp, ha, W_nil, ?_⟩
      rw [encode_append]
      exact .emptyArray (mem_structural' (by decide) rfl (a := []) W_nil W_nil) he
    · refine ⟨a, ['['] ++ a₁ ++ ys ++ e, [], by simp, ha, W_nil, ?_⟩
      rw [encode_append, encode_append, show ['['] ++ a₁ = [] ++ ['['] ++ a₁ by rfl]
      exact .array (mem_structural' (by decide) rfl W_nil ha₁) hys he
  | .object (xs := xs) hx, cs, h => by
    obtain ⟨a, l, r, rfl, ha, hl, hr⟩ := lexes_cons h
    have hl' : l = ['{'] := lexeme_punct hl (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    subst hl'
    rcases members_of_lexes hx hr with he | ⟨a₁, ys, e, rfl, ha₁, hys, he⟩
    · refine ⟨a, ['{'] ++ r, [], by simp, ha, W_nil, ?_⟩
      rw [encode_append]
      exact .emptyObject (mem_structural' (by decide) rfl (a := []) W_nil W_nil) he
    · refine ⟨a, ['{'] ++ a₁ ++ ys ++ e, [], by simp, ha, W_nil, ?_⟩
      rw [encode_append, encode_append, show ['{'] ++ a₁ = [] ++ ['{'] ++ a₁ by rfl]
      exact .object (mem_structural' (by decide) rfl W_nil ha₁) hys he

theorem elems_of_lexes {ts : List Token} : TElems ts → ∀ {cs : List Char}, Lexes cs ts →
    encode cs ∈ endArray.matches' ∨
    (∃ a xs e, cs = a ++ xs ++ e ∧ W a ∧ Elements .rfc8259 (encode xs) ∧ encode e ∈ endArray.matches')
  | .empty, cs, h => by
    obtain ⟨a, a', rfl, ha, ha'⟩ := lexes_punct h (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact Or.inl (mem_structural' (by decide) rfl ha ha')
  | .ne hx, cs, h => Or.inr (elemsNE_of_lexes hx h)

theorem elemsNE_of_lexes {ts : List Token} : TElemsNE ts → ∀ {cs : List Char}, Lexes cs ts →
    ∃ a xs e, cs = a ++ xs ++ e ∧ W a ∧ Elements .rfc8259 (encode xs) ∧ encode e ∈ endArray.matches'
  | .last (v := v) hv, cs, h => by
    obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := lexes_append h
    obtain ⟨a, x, b, rfl, ha, hb, hx⟩ := value_of_lexes hv h₁
    obtain ⟨a₂, a₂', rfl, ha₂, ha₂'⟩ := lexes_punct h₂ (Or.inr (Or.inl ⟨rfl, rfl⟩))
    refine ⟨a, x, b ++ a₂ ++ [']'] ++ a₂', by simp, ha, .one hx, ?_⟩
    exact mem_structural' (by decide) rfl (W_append hb ha₂) ha₂'
  | .cons (v := v) (xs := xs) hv hx, cs, h => by
    obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := lexes_append h
    obtain ⟨c₂, c₃, rfl, h₂, h₃⟩ := lexes_append (ts₁ := [.comma]) h₂
    obtain ⟨a, x, b, rfl, ha, hb, hxv⟩ := value_of_lexes hv h₁
    obtain ⟨a₂, a₂', rfl, ha₂, ha₂'⟩ := lexes_punct h₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    obtain ⟨a₃, ys, e, rfl, ha₃, hys, he⟩ := elemsNE_of_lexes hx h₃
    refine ⟨a, x ++ (b ++ a₂ ++ [','] ++ (a₂' ++ a₃)) ++ ys, e, by simp, ha, ?_, he⟩
    rw [encode_append, encode_append]
    exact .cons hxv (mem_structural' (by decide) rfl (W_append hb ha₂) (W_append ha₂' ha₃)) hys

theorem members_of_lexes {ts : List Token} : TMembers ts → ∀ {cs : List Char}, Lexes cs ts →
    encode cs ∈ endObject.matches' ∨
    (∃ a xs e, cs = a ++ xs ++ e ∧ W a ∧ Members .rfc8259 (encode xs) ∧ encode e ∈ endObject.matches')
  | .empty, cs, h => by
    obtain ⟨a, a', rfl, ha, ha'⟩ := lexes_punct h (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    exact Or.inl (mem_structural' (by decide) rfl ha ha')
  | .ne hx, cs, h => Or.inr (membersNE_of_lexes hx h)

theorem membersNE_of_lexes {ts : List Token} : TMembersNE ts → ∀ {cs : List Char}, Lexes cs ts →
    ∃ a xs e, cs = a ++ xs ++ e ∧ W a ∧ Members .rfc8259 (encode xs) ∧ encode e ∈ endObject.matches'
  | .last (k := k) (v := v) hv, cs, h => by
    obtain ⟨a, l, r, rfl, ha, hl, hr⟩ := lexes_cons h
    obtain ⟨a₁, l₁, r₁, rfl, ha₁, hl₁, hr₁⟩ := lexes_cons hr
    have : l₁ = [':'] := lexeme_punct hl₁ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
    subst this
    obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := lexes_append hr₁
    obtain ⟨a₂, x, b, rfl, ha₂, hb, hxv⟩ := value_of_lexes hv h₁
    obtain ⟨a₃, a₃', rfl, ha₃, ha₃'⟩ := lexes_punct h₂ (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    refine ⟨a, l ++ (a₁ ++ [':'] ++ a₂) ++ x, b ++ a₃ ++ ['}'] ++ a₃', by simp, ha, ?_, ?_⟩
    · rw [encode_append, encode_append]
      exact .one (lexeme_string hl) (mem_structural' (by decide) rfl ha₁ ha₂) hxv
    · exact mem_structural' (by decide) rfl (W_append hb ha₃) ha₃'
  | .cons (k := k) (v := v) (xs := xs) hv hx, cs, h => by
    obtain ⟨a, l, r, rfl, ha, hl, hr⟩ := lexes_cons h
    obtain ⟨a₁, l₁, r₁, rfl, ha₁, hl₁, hr₁⟩ := lexes_cons hr
    have : l₁ = [':'] := lexeme_punct hl₁ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
    subst this
    obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := lexes_append hr₁
    obtain ⟨c₂, c₃, rfl, h₂, h₃⟩ := lexes_append (ts₁ := [.comma]) h₂
    obtain ⟨a₂, x, b, rfl, ha₂, hb, hxv⟩ := value_of_lexes hv h₁
    obtain ⟨a₃, a₃', rfl, ha₃, ha₃'⟩ := lexes_punct h₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    obtain ⟨a₄, ys, e, rfl, ha₄, hys, he⟩ := membersNE_of_lexes hx h₃
    refine ⟨a, l ++ (a₁ ++ [':'] ++ a₂) ++ x ++ (b ++ a₃ ++ [','] ++ (a₃' ++ a₄)) ++ ys, e, by simp, ha, ?_, he⟩
    rw [encode_append, encode_append, encode_append, encode_append]
    exact .cons (lexeme_string hl) (mem_structural' (by decide) rfl ha₁ ha₂) hxv
      (mem_structural' (by decide) rfl (W_append hb ha₃) (W_append ha₃' ha₄)) hys

end

/-- **Soundness**: characters the reader lexes into a `TValue` are a JSON text. -/
theorem text_of_lexes {cs : List Char} {ts : List Token} (hl : Lexes cs ts) (hv : TValue ts) :
    encode cs ∈ language .rfc8259 := by
  obtain ⟨a, v, b, rfl, ha, hb, hval⟩ := value_of_lexes hv hl
  exact ⟨encode a, encode v, encode b, mem_ws_chars.mpr ha, hval, mem_ws_chars.mpr hb, by simp⟩

/-! ## JSON texts are read (completeness) -/

theorem split3 {cs : List Char} {a m b : List UInt8} (h : encode cs = a ++ m ++ b)
    (ha : IsWellFormed a) (hm : IsWellFormed m) (hb : IsWellFormed b) :
    ∃ ca cm cb, cs = ca ++ cm ++ cb ∧ encode ca = a ∧ encode cm = m ∧ encode cb = b := by
  obtain ⟨c₁, cb, rfl, h₁, rfl⟩ := encode_eq_append h (isWellFormed_append ha hm) hb
  obtain ⟨ca, cm, rfl, rfl, rfl⟩ := encode_eq_append h₁ ha hm
  exact ⟨ca, cm, cb, rfl, rfl, rfl, rfl⟩

theorem wf_structural {b : UInt8} (hb : b < 0x80) {w : List UInt8} (h : w ∈ (structural b).matches') :
    IsWellFormed w := good_structural hb w h

/-- `cs` with an encoding in `structural b`: whitespace, the character, whitespace. -/
theorem chars_structural {b : UInt8} {c : Char} (hb : b < 0x80) (hc : c.toNat = b.toNat) {cs : List Char}
    {w : List UInt8} (hw : w ∈ (structural b).matches') (he : encode cs = w) :
    ∃ a a', cs = a ++ [c] ++ a' ∧ W a ∧ W a' :=
  (mem_structural hb hc).mp (he ▸ hw)

theorem tokensOf_W {ws : List Char} (hw : W ws) (X : List Char) : tokensOf (ws ++ X) = tokensOf X :=
  tokensOf_white_append hw X

theorem tokensOf_struct {a a' : List Char} (ha : W a) (ha' : W a') {c : Char} {tok : Token}
    (h : c = '[' ∧ tok = .arrayOpen ∨ c = ']' ∧ tok = .arrayClose ∨ c = '{' ∧ tok = .objectOpen ∨
      c = '}' ∧ tok = .objectClose ∨ c = ',' ∧ tok = .comma ∨ c = ':' ∧ tok = .colon) (X : List Char) :
    tokensOf (a ++ [c] ++ a' ++ X) = (tokensOf X).map (tok :: ·) := by
  rw [List.append_assoc, List.append_assoc, tokensOf_W ha, List.singleton_append, tokensOf_punct h,
    tokensOf_W ha']

theorem follow_struct {a rest : List Char} (ha : W a) {c : Char} (hc : delimiter .rfc8259 c = true) :
    Follow (a ++ c :: rest) := by
  intro y hy
  cases a with
  | nil =>
    have hxy : c = y := by simpa using hy
    subst hxy; exact hc
  | cons x a =>
    have hxy : x = y := by simpa using hy
    subst hxy
    simp [delimiter, ha x (by simp)]

theorem follow_W {a : List Char} (ha : W a) : Follow a := by
  intro y hy
  cases a with
  | nil => simp at hy
  | cons x a =>
    have hxy : x = y := by simpa using hy
    subst hxy
    simp [delimiter, ha x (by simp)]

mutual

theorem tokens_of_value {w : List UInt8} : Value .rfc8259 w → ∀ {cs : List Char}, encode cs = w →
    ∀ {X : List Char}, Follow X → ∃ ts, TValue ts ∧ tokensOf (cs ++ X) = (tokensOf X).map (ts ++ ·)
  | .scalar hs, cs, he, X, hX => by
    rw [← he, mem_scalar] at hs
    rcases hs with rfl | rfl | rfl | hn | ⟨b, rfl, hb⟩
    · exact ⟨[.bool false], .scalar trivial, tokensOf_literal (Or.inr (Or.inl ⟨rfl, rfl⟩)) hX⟩
    · exact ⟨[.null], .scalar trivial, tokensOf_literal (Or.inr (Or.inr ⟨rfl, rfl⟩)) hX⟩
    · exact ⟨[.bool true], .scalar trivial, tokensOf_literal (Or.inl ⟨rfl, rfl⟩) hX⟩
    · obtain ⟨n, hn'⟩ := tokensOf_number hn hX
      exact ⟨[.number n], .scalar trivial, hn'⟩
    · obtain ⟨u, hu⟩ := tokensOf_string hb X
      exact ⟨[.string u], .scalar trivial, hu⟩
  | .emptyArray (a := a) (b := b) ha hb, cs, he, X, hX => by
    obtain ⟨ca, cb, rfl, rfl, rfl⟩ := encode_eq_append he
      (wf_structural (by decide) ha) (wf_structural (by decide) hb)
    obtain ⟨a₁, a₁', rfl, h₁, h₁'⟩ := chars_structural (c := '[') (by decide) rfl ha rfl
    obtain ⟨a₂, a₂', rfl, h₂, h₂'⟩ := chars_structural (c := ']') (by decide) rfl hb rfl
    refine ⟨[.arrayOpen, .arrayClose], .array .empty, ?_⟩
    have := tokensOf_struct h₁ (W_append h₁' h₂) (Or.inl ⟨rfl, rfl⟩) ([']'] ++ a₂' ++ X)
    rw [show a₁ ++ ['['] ++ a₁' ++ (a₂ ++ [']'] ++ a₂') ++ X =
      a₁ ++ ['['] ++ (a₁' ++ a₂) ++ ([']'] ++ a₂' ++ X) by simp, this,
      show [']'] ++ a₂' ++ X = [] ++ [']'] ++ a₂' ++ X by simp,
      tokensOf_struct W_nil h₂' (Or.inr (Or.inl ⟨rfl, rfl⟩)) X]
    cases tokensOf X <;> rfl
  | .array (a := a) (xs := xs) (b := b) ha hx hb, cs, he, X, hX => by
    obtain ⟨ca, cx, cb, rfl, rfl, hcx, rfl⟩ := split3 he (wf_structural (by decide) ha)
      (elements_isWellFormed hx) (wf_structural (by decide) hb)
    obtain ⟨ts, hts, htok⟩ := tokens_of_elements hx hcx (e := cb) (X := X)
      (chars_structural (c := ']') (by decide) rfl hb rfl)
    obtain ⟨a₁, a₁', rfl, h₁, h₁'⟩ := chars_structural (c := '[') (by decide) rfl ha rfl
    refine ⟨.arrayOpen :: (ts ++ [.arrayClose]), .array (.ne hts), ?_⟩
    rw [show a₁ ++ ['['] ++ a₁' ++ cx ++ cb ++ X = a₁ ++ ['['] ++ a₁' ++ (cx ++ (cb ++ X)) by simp,
      tokensOf_struct h₁ h₁' (Or.inl ⟨rfl, rfl⟩), htok]
    cases tokensOf X <;> simp
  | .emptyObject (a := a) (b := b) ha hb, cs, he, X, hX => by
    obtain ⟨ca, cb, rfl, rfl, rfl⟩ := encode_eq_append he
      (wf_structural (by decide) ha) (wf_structural (by decide) hb)
    obtain ⟨a₁, a₁', rfl, h₁, h₁'⟩ := chars_structural (c := '{') (by decide) rfl ha rfl
    obtain ⟨a₂, a₂', rfl, h₂, h₂'⟩ := chars_structural (c := '}') (by decide) rfl hb rfl
    refine ⟨[.objectOpen, .objectClose], .object .empty, ?_⟩
    have := tokensOf_struct h₁ (W_append h₁' h₂) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) (['}'] ++ a₂' ++ X)
    rw [show a₁ ++ ['{'] ++ a₁' ++ (a₂ ++ ['}'] ++ a₂') ++ X =
      a₁ ++ ['{'] ++ (a₁' ++ a₂) ++ (['}'] ++ a₂' ++ X) by simp, this,
      show ['}'] ++ a₂' ++ X = [] ++ ['}'] ++ a₂' ++ X by simp,
      tokensOf_struct W_nil h₂' (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) X]
    cases tokensOf X <;> rfl
  | .object (a := a) (ms := ms) (b := b) ha hm hb, cs, he, X, hX => by
    obtain ⟨ca, cm, cb, rfl, rfl, hcm, rfl⟩ := split3 he (wf_structural (by decide) ha)
      (members_isWellFormed hm) (wf_structural (by decide) hb)
    obtain ⟨ts, hts, htok⟩ := tokens_of_members hm hcm (e := cb) (X := X)
      (chars_structural (c := '}') (by decide) rfl hb rfl)
    obtain ⟨a₁, a₁', rfl, h₁, h₁'⟩ := chars_structural (c := '{') (by decide) rfl ha rfl
    refine ⟨.objectOpen :: (ts ++ [.objectClose]), .object (.ne hts), ?_⟩
    rw [show a₁ ++ ['{'] ++ a₁' ++ cm ++ cb ++ X = a₁ ++ ['{'] ++ a₁' ++ (cm ++ (cb ++ X)) by simp,
      tokensOf_struct h₁ h₁' (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), htok]
    cases tokensOf X <;> simp

theorem tokens_of_elements {w : List UInt8} : Elements .rfc8259 w → ∀ {cs : List Char}, encode cs = w →
    ∀ {e X : List Char}, (∃ a a', e = a ++ [']'] ++ a' ∧ W a ∧ W a') →
    ∃ ts, TElemsNE (ts ++ [.arrayClose]) ∧
      tokensOf (cs ++ (e ++ X)) = (tokensOf X).map (ts ++ .arrayClose :: ·)
  | .one hv, cs, he, e, X, ⟨a, a', hea, ha, ha'⟩ => by
    obtain ⟨tv, htv, htok⟩ := tokens_of_value hv he (X := e ++ X)
      (by rw [hea, List.append_assoc, List.append_assoc]; exact follow_struct ha (by decide))
    refine ⟨tv, .last htv, ?_⟩
    rw [htok, hea, tokensOf_struct ha ha' (Or.inr (Or.inl ⟨rfl, rfl⟩))]
    cases tokensOf X <;> simp
  | .cons (v := v) (s := sp) (vs := vs) hv hs hvs, cs, he, e, X, hee => by
    obtain ⟨cv, cs', cvs, rfl, hcv, rfl, hcvs⟩ := split3 he (value_isWellFormed hv)
      (wf_structural (by decide) hs) (elements_isWellFormed hvs)
    obtain ⟨tvs, htvs, htok'⟩ := tokens_of_elements hvs hcvs (X := X) hee
    obtain ⟨a, a', rfl, ha, ha'⟩ := chars_structural (c := ',') (by decide) rfl hs rfl
    obtain ⟨tv, htv, htok⟩ := tokens_of_value hv hcv (X := a ++ [','] ++ a' ++ cvs ++ (e ++ X))
      (by simp only [List.append_assoc, List.singleton_append]; exact follow_struct ha (by decide))
    refine ⟨tv ++ .comma :: tvs, by simpa using TElemsNE.cons htv htvs, ?_⟩
    rw [show cv ++ (a ++ [','] ++ a') ++ cvs ++ (e ++ X) = cv ++ (a ++ [','] ++ a' ++ cvs ++ (e ++ X)) by simp,
      htok, show a ++ [','] ++ a' ++ cvs ++ (e ++ X) = a ++ [','] ++ a' ++ (cvs ++ (e ++ X)) by simp,
      tokensOf_struct ha ha' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))), htok']
    cases tokensOf X <;> simp

theorem tokens_of_members {w : List UInt8} : Members .rfc8259 w → ∀ {cs : List Char}, encode cs = w →
    ∀ {e X : List Char}, (∃ a a', e = a ++ ['}'] ++ a' ∧ W a ∧ W a') →
    ∃ ts, TMembersNE (ts ++ [.objectClose]) ∧
      tokensOf (cs ++ (e ++ X)) = (tokensOf X).map (ts ++ .objectClose :: ·)
  | .one (k := k) (c := c) (v := v) hk hc hv, cs, he, e, X, ⟨a, a', hea, ha, ha'⟩ => by
    obtain ⟨ck, cc, cv, rfl, rfl, rfl, hcv⟩ := split3 he (good_string _ hk)
      (wf_structural (by decide) hc) (value_isWellFormed hv)
    obtain ⟨tv, htv, htok⟩ := tokens_of_value hv hcv (X := e ++ X)
      (by rw [hea, List.append_assoc, List.append_assoc]; exact follow_struct ha (by decide))
    obtain ⟨body, rfl, hbody⟩ := mem_string.mp hk
    obtain ⟨b₁, b₁', rfl, hb₁, hb₁'⟩ := chars_structural (c := ':') (by decide) rfl hc rfl
    obtain ⟨u, hu⟩ := tokensOf_string hbody (b₁ ++ [':'] ++ b₁' ++ cv ++ (e ++ X))
    refine ⟨.string u :: .colon :: tv, by simpa using TMembersNE.last (k := u) htv, ?_⟩
    rw [show ('"' :: (body ++ ['"'])) ++ (b₁ ++ [':'] ++ b₁') ++ cv ++ (e ++ X) =
      ('"' :: (body ++ ['"'])) ++ (b₁ ++ [':'] ++ b₁' ++ cv ++ (e ++ X)) by simp, hu,
      show b₁ ++ [':'] ++ b₁' ++ cv ++ (e ++ X) = b₁ ++ [':'] ++ b₁' ++ (cv ++ (e ++ X)) by simp,
      tokensOf_struct hb₁ hb₁' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))), htok, hea,
      tokensOf_struct ha ha' (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))]
    cases tokensOf X <;> simp
  | .cons (k := k) (c := c) (v := v) (s := sp) (ms := ms) hk hc hv hs hms, cs, he, e, X, hee => by
    have hkcv : IsWellFormed (k ++ c ++ v) := isWellFormed_append (isWellFormed_append
      (good_string _ hk) (wf_structural (by decide) hc)) (value_isWellFormed hv)
    obtain ⟨c₁, cs', cms, rfl, h₁, rfl, hcms⟩ := split3 he hkcv
      (wf_structural (by decide) hs) (members_isWellFormed hms)
    obtain ⟨ck, cc, cv, rfl, rfl, rfl, hcv⟩ := split3 h₁ (good_string _ hk)
      (wf_structural (by decide) hc) (value_isWellFormed hv)
    obtain ⟨tms, htms, htok'⟩ := tokens_of_members hms hcms (X := X) hee
    obtain ⟨a, a', rfl, ha, ha'⟩ := chars_structural (c := ',') (by decide) rfl hs rfl
    obtain ⟨tv, htv, htok⟩ := tokens_of_value hv hcv (X := a ++ [','] ++ a' ++ cms ++ (e ++ X))
      (by simp only [List.append_assoc, List.singleton_append]; exact follow_struct ha (by decide))
    obtain ⟨body, rfl, hbody⟩ := mem_string.mp hk
    obtain ⟨b₁, b₁', rfl, hb₁, hb₁'⟩ := chars_structural (c := ':') (by decide) rfl hc rfl
    obtain ⟨u, hu⟩ := tokensOf_string hbody (b₁ ++ [':'] ++ b₁' ++ (cv ++ (a ++ [','] ++ a' ++ cms ++ (e ++ X))))
    refine ⟨.string u :: .colon :: (tv ++ .comma :: tms), by simpa using TMembersNE.cons (k := u) htv htms, ?_⟩
    rw [show ('"' :: (body ++ ['"'])) ++ (b₁ ++ [':'] ++ b₁') ++ cv ++ (a ++ [','] ++ a') ++ cms ++ (e ++ X) =
      ('"' :: (body ++ ['"'])) ++ (b₁ ++ [':'] ++ b₁' ++ (cv ++ (a ++ [','] ++ a' ++ cms ++ (e ++ X)))) by simp,
      hu, tokensOf_struct hb₁ hb₁' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))), htok,
      show a ++ [','] ++ a' ++ cms ++ (e ++ X) = a ++ [','] ++ a' ++ (cms ++ (e ++ X)) by simp,
      tokensOf_struct ha ha' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))), htok']
    cases tokensOf X <;> simp

end

/-- **Completeness**: the characters of a JSON text are read into a `TValue`. -/
theorem tokensOf_of_text {w : List UInt8} (h : w ∈ language .rfc8259) {cs : List Char}
    (he : encode cs = w) : ∃ ts, TValue ts ∧ tokensOf cs = some ts := by
  obtain ⟨a, v, b, ha, hv, hb, rfl⟩ := h
  obtain ⟨ca, cv, cb, rfl, rfl, hcv, rfl⟩ := split3 he (good_ws _ ha) (value_isWellFormed hv) (good_ws _ hb)
  have hca := mem_ws_chars.mp ha
  have hcb := mem_ws_chars.mp hb
  obtain ⟨ts, hts, htok⟩ := tokens_of_value hv hcv (follow_W hcb)
  refine ⟨ts, hts, ?_⟩
  have h0 : tokensOf cb = some [] := by
    simpa using tokensOf_W hcb []
  rw [List.append_assoc, tokensOf_W hca, htok, h0]
  simp

/-! ## Numbers in the syntax tree -/

/-- Every number of a syntax tree is finite. -/
def FiniteNums : {i : Silmaril.Formats.JsonIx} → Syn Number i → Prop
  | _, .scalar (some (.number n)) => ∃ d, n = .finite d
  | _, .scalar _ => True
  | _, .list xs => FiniteNums xs
  | _, .map xs => FiniteNums xs
  | _, .nil => True
  | _, .cons v vs => FiniteNums v ∧ FiniteNums vs
  | _, .objNil => True
  | _, .objCons _ v vs => FiniteNums v ∧ FiniteNums vs

theorem mapNumbers?_isSome {f : Number → Option Decimal} (hf : ∀ d, (f (.finite d)).isSome) :
    ∀ {i : Silmaril.Formats.JsonIx} (a : Syn Number i), FiniteNums a → (mapNumbers? f a).isSome
  | _, .scalar none, _ => rfl
  | _, .scalar (some (.bool _)), _ => rfl
  | _, .scalar (some (.string _)), _ => rfl
  | _, .scalar (some (.number n)), h => by
    obtain ⟨d, rfl⟩ := h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hf d)
    simp [mapNumbers?, hx]
  | _, .list xs, h => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (mapNumbers?_isSome hf xs h)
    simp [mapNumbers?, hx]
  | _, .map xs, h => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (mapNumbers?_isSome hf xs h)
    simp [mapNumbers?, hx]
  | _, .nil, _ => rfl
  | _, .cons v vs, h => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (mapNumbers?_isSome hf v h.1)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (mapNumbers?_isSome hf vs h.2)
    simp [mapNumbers?, hx, hy]
  | _, .objNil, _ => rfl
  | _, .objCons _ v vs, h => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (mapNumbers?_isSome hf v h.1)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (mapNumbers?_isSome hf vs h.2)
    simp [mapNumbers?, hx, hy]

/-- Tokens the RFC 8259 lexer makes: no identifiers, finite numbers. -/
def TokOk (t : Token) : Prop :=
  (∀ n, t = .number n → ∃ d, n = .finite d) ∧ ∀ name p, t ≠ .identifier name p

theorem tokOk_suffix {p r : List Token} (h : ∀ t ∈ p ++ r, TokOk t) : ∀ t ∈ r, TokOk t :=
  fun t ht => h t (List.mem_append_right p ht)

theorem finite_ast : ∀ f : Nat,
    (∀ ts a r, (∀ t ∈ ts, TokOk t) → value? .rfc8259 f ts = some (a, r) → FiniteNums a) ∧
    (∀ e ts a r, (∀ t ∈ ts, TokOk t) → array? .rfc8259 f e ts = some (a, r) → FiniteNums a) ∧
    (∀ e ts a r, (∀ t ∈ ts, TokOk t) → object? .rfc8259 f e ts = some (a, r) → FiniteNums a)
  | 0 => by refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [value?, array?, object?]
  | n + 1 => by
    obtain ⟨hV, hA, hO⟩ := finite_ast n
    have sfx := (Silmaril.Proofs.Formats.JsonWire.Parser.sound n).1
    refine ⟨?_, ?_, ?_⟩
    · intro ts a r hok h
      rcases ts with _ | ⟨t, ts⟩
      · simp [value?] at h
      have hok' : ∀ t ∈ ts, TokOk t := fun x hx => hok x (by simp [hx])
      cases t with
      | null => simp [value?] at h; rw [← h.1]; trivial
      | bool => simp [value?] at h; rw [← h.1]; trivial
      | string => simp [value?] at h; rw [← h.1]; trivial
      | number m => simp [value?] at h; rw [← h.1]; exact (hok _ (by simp)).1 m rfl
      | identifier name p => exact absurd rfl ((hok _ (by simp)).2 name p)
      | arrayOpen =>
        simp only [value?] at h
        obtain ⟨⟨xs, r'⟩, hx, h'⟩ := Option.bind_eq_some_iff.mp h
        simp at h'; rw [← h'.1]
        exact hA true ts xs r' hok' hx
      | objectOpen =>
        simp only [value?] at h
        obtain ⟨⟨xs, r'⟩, hx, h'⟩ := Option.bind_eq_some_iff.mp h
        simp at h'; rw [← h'.1]
        exact hO true ts xs r' hok' hx
      | _ => simp [value?] at h
    · intro e ts a r hok h
      unfold array? at h
      split at h
      · split_ifs at h
        simp at h; rw [← h.1]; trivial
      · obtain ⟨⟨v, rest⟩, hv, h'⟩ := Option.bind_eq_some_iff.mp h
        have fv := hV ts v rest hok hv
        obtain ⟨p, rfl, -⟩ := sfx ts v rest hv
        have hok' := tokOk_suffix hok
        rcases rest with _ | ⟨u, rest⟩
        · simp at h'
        cases u <;> simp only [reduceCtorEq] at h'
        all_goals first
          | (simp at h'; done)
          | (simp at h'; rw [← h'.1]; exact ⟨fv, trivial⟩)
          | (obtain ⟨⟨xs, r'⟩, hx, h''⟩ := Option.bind_eq_some_iff.mp h'
             simp at h''; rw [← h''.1]
             exact ⟨fv, hA _ rest xs r' (fun x hx => hok' x (by simp [hx])) hx⟩)
    · intro e ts a r hok h
      rcases Silmaril.Proofs.Formats.JsonWire.Parser.object?_inv h with ⟨rfl, rfl⟩ |
          ⟨k, after, v0, rest0, rfl, -, -⟩
      · simp [object?] at h; rw [← h]; trivial
      have e1 : object? .rfc8259 (n + 1) e (.string k :: .colon :: after) =
          (value? .rfc8259 n after).bind (fun x => match x.2 with
            | .objectClose :: rest => some (.objCons k x.1 .objNil, rest)
            | .comma :: rest => (object? .rfc8259 n false rest).bind (fun y => some (.objCons k x.1 y.1, y.2))
            | _ => none) := rfl
      rw [e1] at h
      have hokA : ∀ t ∈ after, TokOk t := fun x hx => hok x (by simp [hx])
      obtain ⟨⟨v, rest⟩, hv, h'⟩ := Option.bind_eq_some_iff.mp h
      have fv := hV after v rest hokA hv
      obtain ⟨p, rfl, -⟩ := sfx after v rest hv
      have hok' := tokOk_suffix hokA
      rcases rest with _ | ⟨u, rest⟩
      · simp at h'
      cases u <;> simp only [reduceCtorEq] at h'
      all_goals first
        | (simp at h'; done)
        | (simp at h'; rw [← h'.1]; exact ⟨fv, trivial⟩)
        | (obtain ⟨⟨xs, r'⟩, hx, h''⟩ := Option.bind_eq_some_iff.mp h'
           simp at h''; rw [← h''.1]
           exact ⟨fv, hO _ rest xs r' (fun x hx => hok' x (by simp [hx])) hx⟩)

theorem lexeme_ok {l : List Char} {t : Token} (h : Lexeme l t) : TokOk t := by
  cases h with
  | number _ => exact ⟨fun n hn => ⟨_, (Token.number.inj hn).symm⟩, fun _ _ => by simp⟩
  | _ => exact ⟨fun _ hn => by simp at hn, fun _ _ => by simp⟩

theorem lexes_ok {cs : List Char} {ts : List Token} (h : Lexes cs ts) : ∀ t ∈ ts, TokOk t := by
  induction h with
  | nil => simp
  | white _ _ ih => exact ih
  | token hl _ ih =>
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact lexeme_ok hl
    · exact ih t ht

theorem lex_eq_tokensOf {cs : List Char} {l : Lexed} (h : lex .rfc8259 (cs.length + 1) 0 cs = some l) :
    tokensOf cs = some l.tokens := by
  simp [tokensOf, h]

/-- **The RFC 8259 reader accepts exactly the JSON texts**: `JsonWire.parse?` succeeds on the
bytes `w` iff `w` is in `JsonBytes.language .rfc8259`. -/
theorem parse?_isSome_iff (w : List UInt8) :
    (parse? (Silmaril.Formats.Bytes.ofList w)).isSome ↔ w ∈ language .rfc8259 := by
  have hdata : ∀ v : List UInt8, (Silmaril.Formats.Bytes.ofList v).data = v.toByteArray := fun _ => rfl
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    simp only [parse?, parseDecimal?, decode, Option.bind_eq_bind] at hx
    obtain ⟨⟨ast, conc⟩, hd, -⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨s, hs, hd⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨l, hl, hd⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨⟨a, r⟩, hv, hd⟩ := Option.bind_eq_some_iff.mp hd
    have hr : r = [] := by
      simp only at hd
      split_ifs at hd with hre
      exact List.isEmpty_iff.mp hre
    subst hr
    have htok := lex_eq_tokensOf hl
    have hT : TValue l.tokens := (Silmaril.Proofs.Formats.JsonWire.Parser.value?_eq_some_nil_iff
      (f := 2 * l.tokens.length + 1) (by omega)).mp ⟨a, hv⟩
    have hlex := lexes_of_tokensOf s.toList.length s.toList l.tokens le_rfl htok
    have := text_of_lexes hlex hT
    rw [← fromUTF8?_eq_some hs, hdata, List.data_toByteArray] at this
    exact this
  · intro h
    obtain ⟨cs, rfl⟩ := isWellFormed_iff_exists_chars.mp (language_isWellFormed h)
    change encode cs ∈ language .rfc8259 at h
    change (parse? (Silmaril.Formats.Bytes.ofList (encode cs))).isSome = true
    obtain ⟨s, hs, hcs⟩ := fromUTF8?_encode cs
    obtain ⟨ts, hT, htok⟩ := tokensOf_of_text h rfl
    have htok0 := htok
    rw [← hcs] at htok
    obtain ⟨l, hl, hlt⟩ := Option.map_eq_some_iff.mp htok
    obtain ⟨a, ha⟩ := (Silmaril.Proofs.Formats.JsonWire.Parser.value?_eq_some_nil_iff
      (f := 2 * ts.length + 1) (by omega)).mpr hT
    have hok := lexes_ok (lexes_of_tokensOf cs.length cs ts le_rfl htok0)
    have hfin := (finite_ast (2 * ts.length + 1)).1 ts a [] hok ha
    have hdec : decode .rfc8259 (Silmaril.Formats.Bytes.ofList (encode cs)) = some (a, l.concrete) := by
      simp only [decode, hdata, hs, Option.bind_eq_bind, Option.bind_some, hl, hlt, ha]
      rfl
    simp only [parse?, parseDecimal?, hdec, Option.bind_eq_bind, Option.bind_some]
    refine mapNumbers?_isSome ?_ a hfin
    intro d; rfl

end Silmaril.Proofs.Formats.JsonWire.Rfc8259

end
