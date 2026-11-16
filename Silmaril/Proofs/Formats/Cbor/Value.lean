module

public import Silmaril.Formats.Cbor.Value.Defs
import Silmaril.Proofs.Formats.Cbor.WellFormed
import Mathlib.Tactic.Ring

/-! # Proofs: CBOR values and the definite-length codec (`Silmaril.Formats.Cbor.Value.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.Value

open Silmaril.Formats.Cbor
open Silmaril.Proofs.Formats.Cbor.WellFormed (toNat_ofNat_of_lt head_decode readArg_ext)

/-! ## Big-endian bytes -/

theorem foldl_be (a : Nat) (l : List UInt8) :
    l.foldl (fun a b => a * 256 + b.toNat) a = a * 256 ^ l.length + beNat l := by
  induction l generalizing a with
  | nil => simp [beNat]
  | cons x l ih =>
    simp only [List.foldl_cons, beNat, List.length_cons] at ih ⊢
    rw [ih, ih (0 * 256 + x.toNat)]
    ring

theorem length_beBytes (k n : Nat) : (beBytes k n).length = k := by
  induction k <;> simp [beBytes, *]

theorem beNat_cons (x : UInt8) (l : List UInt8) :
    beNat (x :: l) = x.toNat * 256 ^ l.length + beNat l := by
  simp only [beNat, List.foldl_cons]
  rw [foldl_be]
  simp [beNat]

theorem beNat_beBytes (k n : Nat) : beNat (beBytes k n) = n % 256 ^ k := by
  induction k with
  | zero => simp [beBytes, beNat, Nat.mod_one]
  | succ k ih =>
    rw [beBytes, beNat_cons, length_beBytes, ih, UInt8.toNat_ofNat',
      show (2 : Nat) ^ 8 = 256 from rfl, show (256 : Nat) ^ (k + 1) = 256 ^ k * 256 from pow_succ 256 k,
      Nat.mod_mul]
    ring

theorem beNat_beBytes_of_lt {k n : Nat} (h : n < 256 ^ k) : beNat (beBytes k n) = n := by
  rw [beNat_beBytes, Nat.mod_eq_of_lt h]

/-! ## Heads -/

theorem head_encodeHead {mt n : Nat} (hn : n < 2 ^ 64) : Head mt n (encodeHead mt n) := by
  unfold encodeHead
  split_ifs with h1 h2 h3 h4
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr ⟨24, 1, _, rfl, length_beBytes _ _, beNat_beBytes_of_lt (by omega), rfl⟩
  · exact Or.inr ⟨25, 2, _, rfl, length_beBytes _ _, beNat_beBytes_of_lt (by omega), rfl⟩
  · exact Or.inr ⟨26, 4, _, rfl, length_beBytes _ _, beNat_beBytes_of_lt (by omega), rfl⟩
  · exact Or.inr ⟨27, 8, _, rfl, length_beBytes _ _, beNat_beBytes_of_lt (by omega), rfl⟩

theorem encodeHead_length_pos (mt n : Nat) : 1 ≤ (encodeHead mt n).length := by
  unfold encodeHead; split_ifs <;> simp

/-! ## `decode` inverts `encode` -/

theorem encode_length_pos (v : Value) : 1 ≤ v.encode.length := by
  cases v with
  | simple n => simp only [Value.encode]; split_ifs <;> simp
  | float => simp [Value.encode]
  | _ =>
    simp only [Value.encode, List.length_append]
    have := encodeHead_length_pos 0 0
    first
      | have := encodeHead_length_pos 0 ‹_›; omega
      | have := encodeHead_length_pos 1 ‹_›; omega
      | have := encodeHead_length_pos 2 (List.length ‹_›); omega
      | have := encodeHead_length_pos 3 (List.length ‹_›); omega
      | have := encodeHead_length_pos 4 (List.length ‹_›); omega
      | have := encodeHead_length_pos 5 (List.length ‹_›); omega
      | have := encodeHead_length_pos 6 ‹_›; omega

/-- What a head of major type `mt < 7` gives the decoder. -/
theorem encodeHead_decode {mt a : Nat} (hmt : mt < 7) (ha : a < 2 ^ 64) (rest : List UInt8) :
    ∃ b ext, encodeHead mt a = b :: ext ∧ b.toNat / 32 = mt ∧ b.toNat % 32 < 28 ∧
      readArg (b.toNat % 32) (ext ++ rest) = some (a, rest) :=
  head_decode (by omega) (head_encodeHead ha) rest

/-- `decodeItem` on a head of major type `mt < 7` followed by `rest`. -/
theorem decodeItem_headed {mt a : Nat} (hmt : mt < 7) (ha : a < 2 ^ 64) (m : Nat)
    (rest : List UInt8) :
    decodeItem (m + 1) (encodeHead mt a ++ rest) =
      if mt = 0 then some (.uint a, rest)
      else if mt = 1 then some (.nint a, rest)
      else if mt = 2 then
        (if a ≤ rest.length then some (.bytes (rest.take a), rest.drop a) else none)
      else if mt = 3 then
        (if a ≤ rest.length then some (.text (rest.take a), rest.drop a) else none)
      else if mt = 4 then (decodeList m a rest).map fun p => (.array p.1, p.2)
      else if mt = 5 then (decodeMap m a rest).map fun p => (.map p.1, p.2)
      else (decodeItem m rest).map fun p => (.tag a p.1, p.2) := by
  obtain ⟨b, ext, he, hb1, hb2, hra⟩ := encodeHead_decode hmt ha rest
  rw [he, List.cons_append, decodeItem]
  simp only [hb1, show ¬ 28 ≤ b.toNat % 32 by omega, show ¬ mt = 7 by omega, ↓reduceIte, hra,
    Option.bind_some]

mutual

theorem decodeItem_encode (v : Value) (hv : v.Encodable) :
    ∀ n r, 2 * v.encode.length ≤ n → decodeItem n (v.encode ++ r) = some (v, r) := by
  intro n r hn
  have hpos := encode_length_pos v
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  match v, hv with
  | .uint a, hv =>
    simp only [Value.encode]
    rw [decodeItem_headed (by omega) hv]; rfl
  | .nint a, hv =>
    simp only [Value.encode]
    rw [decodeItem_headed (by omega) hv]; rfl
  | .bytes b, hv =>
    simp only [Value.encode, List.append_assoc]
    rw [decodeItem_headed (by omega) hv]
    simp
  | .text t, hv =>
    simp only [Value.encode, List.append_assoc]
    rw [decodeItem_headed (by omega) hv]
    simp
  | .array xs, ⟨hl, hx⟩ =>
    have h1 := encodeHead_length_pos 4 xs.length
    simp only [Value.encode, List.length_append] at hn
    simp only [Value.encode, List.append_assoc]
    rw [decodeItem_headed (by omega) hl]
    simp only [show ¬ (4 = 0) by omega, show ¬ (4 = 1) by omega, show ¬ (4 = 2) by omega,
      show ¬ (4 = 3) by omega, ↓reduceIte, decodeList_encode xs hx m r (by omega), Option.map_some]
  | .map kvs, ⟨hl, hx⟩ =>
    have h1 := encodeHead_length_pos 5 kvs.length
    simp only [Value.encode, List.length_append] at hn
    simp only [Value.encode, List.append_assoc]
    rw [decodeItem_headed (by omega) hl]
    simp only [show ¬ (5 = 0) by omega, show ¬ (5 = 1) by omega, show ¬ (5 = 2) by omega,
      show ¬ (5 = 3) by omega, show ¬ (5 = 4) by omega, ↓reduceIte,
      decodeMap_encode kvs hx m r (by omega), Option.map_some]
  | .tag a w, ⟨ha, hw⟩ =>
    have h1 := encodeHead_length_pos 6 a
    simp only [Value.encode, List.length_append] at hn
    simp only [Value.encode, List.append_assoc]
    rw [decodeItem_headed (by omega) ha]
    simp only [show ¬ (6 = 0) by omega, show ¬ (6 = 1) by omega, show ¬ (6 = 2) by omega,
      show ¬ (6 = 3) by omega, show ¬ (6 = 4) by omega, show ¬ (6 = 5) by omega, ↓reduceIte,
      decodeItem_encode w hw m r (by omega), Option.map_some]
  | .simple k, hv =>
    simp only [Value.encode]
    by_cases hk : k < 24
    · have hb := toNat_ofNat_of_lt (n := 0xE0 + k) (by omega)
      simp only [hk, ↓reduceIte, List.singleton_append, decodeItem, hb,
        show (0xE0 + k) / 32 = 7 by omega, show (0xE0 + k) % 32 = k by omega,
        show ¬ 28 ≤ k by omega]
    · have h32 : 32 ≤ k ∧ k < 256 := by rcases hv with h | h <;> omega
      have hr := readArg_ext (ai := 24) rfl (ext := [UInt8.ofNat k]) rfl r
      rw [show beNat [UInt8.ofNat k] = k by
        simp [beNat, UInt8.toNat_ofNat']; omega] at hr
      simp only [hk, ↓reduceIte, List.cons_append, decodeItem]
      simp only [show (0xF8 : UInt8).toNat = 248 from rfl, show ¬ 28 ≤ 248 % 32 by decide,
        show 248 / 32 = 7 from rfl, show 248 % 32 = 24 from rfl, ↓reduceIte,
        show ¬ (24 < 24) by decide]
      rw [show [UInt8.ofNat k] ++ r = UInt8.ofNat k :: r from rfl] at hr
      simp [hr, h32.1]
  | .float w bits, ⟨hw, hb⟩ =>
    have hai : floatAi w = 25 ∧ aiWidth 25 = w ∧ argWidth 25 = some w ∨
        floatAi w = 26 ∧ aiWidth 26 = w ∧ argWidth 26 = some w ∨
        floatAi w = 27 ∧ aiWidth 27 = w ∧ argWidth 27 = some w := by
      rcases hw with rfl | rfl | rfl <;> simp [floatAi, aiWidth, argWidth]
    simp only [Value.encode, List.cons_append]
    rcases hai with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    · have hr := readArg_ext h3 (length_beBytes w bits) r
      rw [beNat_beBytes_of_lt hb] at hr
      simp only [decodeItem, h1]
      simp [hr, h2]

theorem decodeList_encode (xs : List Value) (hx : ListEncodable xs) :
    ∀ f r, 2 * (encodeList xs).length + 1 ≤ f →
      decodeList f xs.length (encodeList xs ++ r) = some (xs, r) := by
  intro f r hf
  match xs, hx with
  | [], _ => cases f <;> rfl
  | x :: xs, ⟨h1, h2⟩ =>
    have := encode_length_pos x
    simp only [encodeList, List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [encodeList, List.length_cons, List.append_assoc, decodeList,
      decodeItem_encode x h1 g _ (by omega), Option.bind_some,
      decodeList_encode xs h2 g r (by omega), Option.map_some]

theorem decodeMap_encode (kvs : List (Value × Value)) (hx : MapEncodable kvs) :
    ∀ f r, 2 * (encodeMap kvs).length + 1 ≤ f →
      decodeMap f kvs.length (encodeMap kvs ++ r) = some (kvs, r) := by
  intro f r hf
  match kvs, hx with
  | [], _ => cases f <;> rfl
  | (k, v) :: kvs, ⟨h1, h2, h3⟩ =>
    have := encode_length_pos k
    have := encode_length_pos v
    simp only [encodeMap, List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [encodeMap, List.length_cons, List.append_assoc, decodeMap,
      decodeItem_encode k h1 g _ (by omega), Option.bind_some,
      decodeItem_encode v h2 g _ (by omega), decodeMap_encode kvs h3 g r (by omega),
      Option.map_some]

end

theorem decode_encode (v : Value) (hv : v.Encodable) : decode v.encode = some v := by
  have := decodeItem_encode v hv (2 * v.encode.length + 2) [] (by omega)
  rw [List.append_nil] at this
  simp [decode, this]

/-! ## Encodings are well-formed -/

mutual

theorem encode_item (v : Value) (hv : v.Encodable) : Item v.encode := by
  match v, hv with
  | .uint a, hv => exact .uint (head_encodeHead hv)
  | .nint a, hv => exact .nint (head_encodeHead hv)
  | .bytes b, hv => exact .string (Or.inl rfl) ⟨_, _, b, head_encodeHead hv, rfl, rfl⟩
  | .text t, hv => exact .string (Or.inr rfl) ⟨_, _, t, head_encodeHead hv, rfl, rfl⟩
  | .array xs, ⟨hl, hx⟩ => exact .array (head_encodeHead hl) (encodeList_items xs hx)
  | .map kvs, ⟨hl, hx⟩ => exact .map (head_encodeHead hl) (encodeMap_items kvs hx)
  | .tag a w, ⟨ha, hw⟩ => exact .tag (head_encodeHead ha) (encode_item w hw)
  | .simple k, hv =>
    simp only [Value.encode]
    split_ifs with hk
    · exact .simple hk
    · have h32 : 32 ≤ k ∧ k < 256 := by rcases hv with h | h <;> omega
      exact .simpleByte (by rw [toNat_ofNat_of_lt h32.2]; exact h32.1)
  | .float w bits, ⟨hw, hb⟩ =>
    have : (floatAi w = 25 ∧ argWidth 25 = some w) ∨ (floatAi w = 26 ∧ argWidth 26 = some w) ∨
        (floatAi w = 27 ∧ argWidth 27 = some w) := by
      rcases hw with rfl | rfl | rfl <;> simp [floatAi, argWidth]
    simp only [Value.encode]
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1] <;> exact .float h2 (by omega) (length_beBytes _ _)

theorem encodeList_items (xs : List Value) (hx : ListEncodable xs) :
    Items xs.length (encodeList xs) := by
  match xs, hx with
  | [], _ => exact .nil
  | x :: xs, ⟨h1, h2⟩ => exact .cons (encode_item x h1) (encodeList_items xs h2)

theorem encodeMap_items (kvs : List (Value × Value)) (hx : MapEncodable kvs) :
    Items (2 * kvs.length) (encodeMap kvs) := by
  match kvs, hx with
  | [], _ => exact .nil
  | (k, v) :: kvs, ⟨h1, h2, h3⟩ =>
    rw [List.length_cons, show 2 * (kvs.length + 1) = 2 * kvs.length + 1 + 1 by omega]
    simp only [encodeMap, List.append_assoc]
    exact .cons (encode_item k h1) (.cons (encode_item v h2) (encodeMap_items kvs h3))

end

end Silmaril.Proofs.Formats.Cbor.Value

end
