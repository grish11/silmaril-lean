module

public import Silmaril.Formats.Cbor.Events.Defs
import Silmaril.Proofs.Formats.Cbor.WellFormed
import Silmaril.Proofs.Formats.Cbor.Value
import Mathlib.Tactic.Ring

/-! # Proofs: CBOR event streams (`Silmaril.Formats.Cbor.Events.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.Events

open Silmaril.Formats.Cbor
open Silmaril.Proofs.Formats.Cbor.WellFormed (toNat_ofNat_of_lt readArg_ext item_head item_length)
open Silmaril.Proofs.Formats.Cbor.Value (head_encodeHead encodeHead_length_pos encodeHead_decode
  length_beBytes beNat_beBytes_of_lt)

theorem encodeEvents_append (a b : List Event) :
    encodeEvents (a ++ b) = encodeEvents a ++ encodeEvents b := List.flatMap_append

theorem encodeEvents_cons (e : Event) (es : List Event) :
    encodeEvents (e :: es) = e.encode ++ encodeEvents es := List.flatMap_cons

theorem encodeEvents_nil : encodeEvents [] = [] := rfl

/-! ## Event streams encode to well-formed items -/

theorem chunks_of {mt : Nat} (cs : List (List UInt8))
    (h : ∀ c ∈ cs, c.length < 2 ^ 64) :
    Chunks mt (cs.flatMap fun c => encodeHead mt c.length ++ c) := by
  refine ⟨cs.map fun c => encodeHead mt c.length ++ c, by clear h; induction cs <;> simp_all, ?_⟩
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact ⟨c.length, _, c, head_encodeHead (h c hc), rfl, rfl⟩

theorem encodeEvents_map_bytes (cs : List (List UInt8)) :
    encodeEvents (cs.map .bytes) = cs.flatMap fun c => encodeHead 2 c.length ++ c := by
  induction cs <;> simp_all [encodeEvents, Event.encode]

theorem encodeEvents_map_text (cs : List (List UInt8)) :
    encodeEvents (cs.map .text) = cs.flatMap fun c => encodeHead 3 c.length ++ c := by
  induction cs <;> simp_all [encodeEvents, Event.encode]

mutual

theorem itemEv_item {es : List Event} : ItemEv es → Item (encodeEvents es)
  | .uint h => by simpa [encodeEvents, Event.encode] using Item.uint (head_encodeHead h)
  | .nint h => by simpa [encodeEvents, Event.encode] using Item.nint (head_encodeHead h)
  | .bytes (b := b) h => by
    simpa [encodeEvents, Event.encode] using
      Item.string (Or.inl rfl) ⟨b.length, _, b, head_encodeHead h, rfl, rfl⟩
  | .text (t := t) h => by
    simpa [encodeEvents, Event.encode] using
      Item.string (Or.inr rfl) ⟨t.length, _, t, head_encodeHead h, rfl, rfl⟩
  | .indefBytes (cs := cs) h => by
    rw [encodeEvents_append, encodeEvents_cons, encodeEvents_map_bytes]
    exact Item.indefString (mt := 2) (Or.inl rfl) (chunks_of cs h)
  | .indefText (cs := cs) h => by
    rw [encodeEvents_append, encodeEvents_cons, encodeEvents_map_text]
    exact Item.indefString (mt := 3) (Or.inr rfl) (chunks_of cs h)
  | .array (n := n) (es := es) h hx => by
    rw [encodeEvents_append, encodeEvents_cons]
    simpa [Event.encode, encodeEvents] using Item.array (head_encodeHead h) (itemsEv_items hx)
  | .indefArray hx => by
    rw [encodeEvents_append, encodeEvents_cons]
    exact Item.indefArray (itemsEv_items hx)
  | .map (n := n) (es := es) h hx => by
    rw [encodeEvents_append, encodeEvents_cons]
    simpa [Event.encode, encodeEvents] using Item.map (head_encodeHead h) (itemsEv_items hx)
  | .indefMap hx => by
    rw [encodeEvents_append, encodeEvents_cons]
    exact Item.indefMap (itemsEv_items hx)
  | .tag h hx => by
    rw [encodeEvents_cons]
    exact Item.tag (head_encodeHead h) (itemEv_item hx)
  | .simple (n := n) hv => by
    simp only [encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, Event.encode]
    split_ifs with hk
    · exact .simple hk
    · have h32 : 32 ≤ n ∧ n < 256 := by rcases hv with h | h <;> omega
      exact .simpleByte (by rw [toNat_ofNat_of_lt h32.2]; exact h32.1)
  | .float (w := w) hw hb => by
    have : (floatAi w = 25 ∧ argWidth 25 = some w) ∨ (floatAi w = 26 ∧ argWidth 26 = some w) ∨
        (floatAi w = 27 ∧ argWidth 27 = some w) := by
      rcases hw with rfl | rfl | rfl <;> simp [floatAi, argWidth]
    simp only [encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, Event.encode]
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1] <;> exact .float h2 (by omega) (length_beBytes _ _)

theorem itemsEv_items {k : Nat} {es : List Event} : ItemsEv k es → Items k (encodeEvents es)
  | .nil => .nil
  | .cons he hf => by
    rw [encodeEvents_append]
    exact .cons (itemEv_item he) (itemsEv_items hf)

end

/-! ## Decoding recovers the events -/

theorem encodeEvents_length_pos {es : List Event} (h : ItemEv es) : 1 ≤ (encodeEvents es).length :=
  item_length (itemEv_item h)

theorem encodeEvents_head {es : List Event} (h : ItemEv es) :
    ∃ b t, encodeEvents es = b :: t ∧ b ≠ breakByte :=
  item_head (itemEv_item h)

/-- `decodeEv` on a head of major type `mt < 7` followed by `rest`. -/
theorem decodeEv_headed {mt a : Nat} (hmt : mt < 7) (ha : a < 2 ^ 64) (m : Nat)
    (rest : List UInt8) :
    decodeEv (m + 1) (encodeHead mt a ++ rest) =
      if mt = 0 then some ([.uint a], rest)
      else if mt = 1 then some ([.nint a], rest)
      else if mt = 2 then
        (if a ≤ rest.length then some ([.bytes (rest.take a)], rest.drop a) else none)
      else if mt = 3 then
        (if a ≤ rest.length then some ([.text (rest.take a)], rest.drop a) else none)
      else if mt = 4 then (decodeEvN m a rest).map fun p =>
        (.beginArray (some a) :: p.1 ++ [.endArray (some a)], p.2)
      else if mt = 5 then (decodeEvN m (2 * a) rest).map fun p =>
        (.beginMap (some a) :: p.1 ++ [.endMap (some a)], p.2)
      else (decodeEv m rest).map fun p => (.tag a :: p.1, p.2) := by
  obtain ⟨b, ext, he, hb1, hb2, hra⟩ := encodeHead_decode hmt ha rest
  rw [he, List.cons_append, decodeEv]
  simp only [hb1, show ¬ b.toNat % 32 = 31 by omega, show ¬ 28 ≤ b.toNat % 32 by omega,
    show ¬ mt = 7 by omega, ↓reduceIte, hra, Option.bind_some]

theorem decodeChunks_encode {mt : Nat} (hmt : mt = 2 ∨ mt = 3) (cs : List (List UInt8))
    (h : ∀ c ∈ cs, c.length < 2 ^ 64) : ∀ f r,
      (cs.flatMap fun c => encodeHead mt c.length ++ c).length + 1 ≤ f →
      decodeChunks f mt ((cs.flatMap fun c => encodeHead mt c.length ++ c) ++ breakByte :: r) =
        some (cs, r) := by
  induction cs with
  | nil =>
    intro f r hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [decodeChunks]
  | cons c cs ih =>
    intro f r hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hc := h c (by simp)
    obtain ⟨b, ext, he, hb1, hb2, hra⟩ := encodeHead_decode (mt := mt) (by omega) hc
      (c ++ ((cs.flatMap fun c => encodeHead mt c.length ++ c) ++ breakByte :: r))
    have hne : b ≠ breakByte := by
      rintro rfl; revert hb1; simp [breakByte]; omega
    have hlen := encodeHead_length_pos mt c.length
    simp only [List.flatMap_cons, List.length_append] at hf
    have hrest := ih (fun x hx => h x (by simp [hx])) g r (by omega)
    simp only [List.flatMap_cons, List.append_assoc, he, List.cons_append, decodeChunks, hne,
      ↓reduceIte, hb1, hb2, and_self, hra, Option.bind_some, List.length_append, Nat.le_add_right,
      List.drop_left', List.take_left', hrest, Option.map_some]

mutual

theorem decodeEv_encode {es : List Event} (h : ItemEv es) :
    ∀ n r, 2 * (encodeEvents es).length ≤ n → decodeEv n (encodeEvents es ++ r) = some (es, r) := by
  intro n r hn
  have hpos := encodeEvents_length_pos h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  match es, h with
  | _, .uint hv =>
    simp only [encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, Event.encode]
    rw [decodeEv_headed (by omega) hv]; rfl
  | _, .nint hv =>
    simp only [encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, Event.encode]
    rw [decodeEv_headed (by omega) hv]; rfl
  | _, .bytes hv =>
    simp only [encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, Event.encode,
      List.append_assoc]
    rw [decodeEv_headed (by omega) hv]; simp
  | _, .text hv =>
    simp only [encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, Event.encode,
      List.append_assoc]
    rw [decodeEv_headed (by omega) hv]; simp
  | _, .indefBytes (cs := cs) hc =>
    rw [encodeEvents_append, encodeEvents_cons, encodeEvents_map_bytes] at hn ⊢
    simp only [Event.encode, encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append, List.length_cons] at hn ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append,
      decodeEv]
    simp only [show (0x5F : UInt8).toNat = 95 from rfl, show 95 % 32 = 31 from rfl,
      show 95 / 32 = 2 from rfl, ↓reduceIte]
    rw [show (0xFF : UInt8) :: r = breakByte :: r from rfl,
      decodeChunks_encode (Or.inl rfl) cs hc m r (by omega)]
    rfl
  | _, .indefText (cs := cs) hc =>
    rw [encodeEvents_append, encodeEvents_cons, encodeEvents_map_text] at hn ⊢
    simp only [Event.encode, encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append, List.length_cons] at hn ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append,
      decodeEv]
    simp only [show (0x7F : UInt8).toNat = 127 from rfl, show 127 % 32 = 31 from rfl,
      show 127 / 32 = 3 from rfl, ↓reduceIte, show ¬ (3 = 2) by omega]
    rw [show (0xFF : UInt8) :: r = breakByte :: r from rfl,
      decodeChunks_encode (Or.inr rfl) cs hc m r (by omega)]
    rfl
  | _, .array (n := a) (es := es) ha hx =>
    have := encodeHead_length_pos 4 a
    rw [encodeEvents_append, encodeEvents_cons] at hn ⊢
    simp only [Event.encode, encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append] at hn ⊢
    rw [List.append_assoc, decodeEv_headed (by omega) ha]
    simp only [show ¬ (4 = 0) by omega, show ¬ (4 = 1) by omega, show ¬ (4 = 2) by omega,
      show ¬ (4 = 3) by omega, ↓reduceIte]
    rw [show List.flatMap Event.encode es = encodeEvents es from rfl,
      decodeEvN_encode hx m r (by simp only [encodeEvents] at *; omega)]
    rfl
  | _, .indefArray (es := es) hx =>
    rw [encodeEvents_append, encodeEvents_cons] at hn ⊢
    simp only [Event.encode, List.length_append, List.length_cons, List.length_nil] at hn ⊢
    simp only [encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, Event.encode,
      List.cons_append, List.append_assoc, List.nil_append,
      decodeEv] at hn ⊢
    simp only [show (0x9F : UInt8).toNat = 159 from rfl, show 159 % 32 = 31 from rfl,
      show 159 / 32 = 4 from rfl, ↓reduceIte, show ¬ (4 = 2) by omega, show ¬ (4 = 3) by omega]
    rw [show (0xFF : UInt8) :: r = breakByte :: r from rfl,
      show List.flatMap Event.encode es = encodeEvents es from rfl,
      decodeEvUntilBreak_encode hx m r (by simp only [encodeEvents] at *; omega)]
    rfl
  | _, .map (n := a) (es := es) ha hx =>
    have := encodeHead_length_pos 5 a
    rw [encodeEvents_append, encodeEvents_cons] at hn ⊢
    simp only [Event.encode, encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append] at hn ⊢
    rw [List.append_assoc, decodeEv_headed (by omega) ha]
    simp only [show ¬ (5 = 0) by omega, show ¬ (5 = 1) by omega, show ¬ (5 = 2) by omega,
      show ¬ (5 = 3) by omega, show ¬ (5 = 4) by omega, ↓reduceIte]
    rw [show List.flatMap Event.encode es = encodeEvents es from rfl,
      decodeEvN_encode hx m r (by simp only [encodeEvents] at *; omega)]
    rfl
  | _, .indefMap (es := es) hx =>
    rw [encodeEvents_append, encodeEvents_cons] at hn ⊢
    simp only [Event.encode, List.length_append, List.length_cons, List.length_nil] at hn ⊢
    simp only [encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, Event.encode,
      List.cons_append, List.append_assoc, List.nil_append,
      decodeEv] at hn ⊢
    simp only [show (0xBF : UInt8).toNat = 191 from rfl, show 191 % 32 = 31 from rfl,
      show 191 / 32 = 5 from rfl, ↓reduceIte, show ¬ (5 = 2) by omega, show ¬ (5 = 3) by omega,
      show ¬ (5 = 4) by omega]
    rw [show (0xFF : UInt8) :: r = breakByte :: r from rfl,
      show List.flatMap Event.encode es = encodeEvents es from rfl,
      decodeEvPairs_encode hx (by omega) m r (by simp only [encodeEvents] at *; omega)]
    rfl
  | _, .tag (n := a) (es := es) ha hx =>
    have := encodeHead_length_pos 6 a
    rw [encodeEvents_cons] at hn ⊢
    simp only [Event.encode, List.length_append] at hn ⊢
    rw [List.append_assoc, decodeEv_headed (by omega) ha]
    simp only [show ¬ (6 = 0) by omega, show ¬ (6 = 1) by omega, show ¬ (6 = 2) by omega,
      show ¬ (6 = 3) by omega, show ¬ (6 = 4) by omega, show ¬ (6 = 5) by omega, ↓reduceIte,
      decodeEv_encode hx m r (by omega), Option.map_some]
  | _, .simple (n := k) hv =>
    simp only [encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, Event.encode]
    by_cases hk : k < 24
    · have hb := toNat_ofNat_of_lt (n := 0xE0 + k) (by omega)
      simp only [hk, ↓reduceIte, List.singleton_append, decodeEv, hb,
        show (0xE0 + k) / 32 = 7 by omega, show (0xE0 + k) % 32 = k by omega,
        show ¬ 28 ≤ k by omega, show ¬ k = 31 by omega]
    · have h32 : 32 ≤ k ∧ k < 256 := by rcases hv with h | h <;> omega
      have hr := readArg_ext (ai := 24) rfl (ext := [UInt8.ofNat k]) rfl r
      rw [show beNat [UInt8.ofNat k] = k by
        simp [beNat, UInt8.toNat_ofNat']; omega] at hr
      simp only [hk, ↓reduceIte, List.cons_append, decodeEv]
      simp only [show (0xF8 : UInt8).toNat = 248 from rfl, show ¬ 28 ≤ 248 % 32 by decide,
        show 248 / 32 = 7 from rfl, show 248 % 32 = 24 from rfl, ↓reduceIte,
        show ¬ (24 < 24) by decide, show ¬ (24 = 31) by decide]
      rw [show [UInt8.ofNat k] ++ r = UInt8.ofNat k :: r from rfl] at hr
      simp [hr, h32.1]
  | _, .float (w := w) (bits := bits) hw hb =>
    have hai : floatAi w = 25 ∧ aiWidth 25 = w ∧ argWidth 25 = some w ∨
        floatAi w = 26 ∧ aiWidth 26 = w ∧ argWidth 26 = some w ∨
        floatAi w = 27 ∧ aiWidth 27 = w ∧ argWidth 27 = some w := by
      rcases hw with rfl | rfl | rfl <;> simp [floatAi, aiWidth, argWidth]
    simp only [encodeEvents, List.flatMap_cons, List.flatMap_nil, List.append_nil, Event.encode,
      List.cons_append]
    rcases hai with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    · have hr := readArg_ext h3 (length_beBytes w bits) r
      rw [beNat_beBytes_of_lt hb] at hr
      simp only [decodeEv, h1]
      simp [hr, h2]

theorem decodeEvN_encode {k : Nat} {es : List Event} (h : ItemsEv k es) :
    ∀ f r, 2 * (encodeEvents es).length + 1 ≤ f →
      decodeEvN f k (encodeEvents es ++ r) = some (es, r) := by
  intro f r hf
  match k, es, h with
  | _, _, .nil => cases f <;> rfl
  | _, _, .cons (k := k) (es := es) (fs := fs) he hfs =>
    have := encodeEvents_length_pos he
    rw [encodeEvents_append] at hf ⊢
    simp only [List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [List.append_assoc, decodeEvN, decodeEv_encode he g _ (by omega), Option.bind_some,
      decodeEvN_encode hfs g r (by omega), Option.map_some]

theorem decodeEvUntilBreak_encode {k : Nat} {es : List Event} (h : ItemsEv k es) :
    ∀ f r, 2 * (encodeEvents es).length + 1 ≤ f →
      decodeEvUntilBreak f (encodeEvents es ++ breakByte :: r) = some (es, r) := by
  intro f r hf
  match k, es, h with
  | _, _, .nil =>
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [decodeEvUntilBreak, encodeEvents]
  | _, _, .cons (k := k) (es := es) (fs := fs) he hfs =>
    have := encodeEvents_length_pos he
    rw [encodeEvents_append] at hf ⊢
    simp only [List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hs := decodeEv_encode he g (encodeEvents fs ++ breakByte :: r) (by omega)
    have hrec := decodeEvUntilBreak_encode hfs g r (by omega)
    obtain ⟨b, t, hbt, hb⟩ := encodeEvents_head he
    rw [List.append_assoc, hbt, List.cons_append]
    rw [hbt, List.cons_append] at hs
    simp only [decodeEvUntilBreak, hb, ↓reduceIte, hs, Option.bind_some, hrec, Option.map_some]

theorem decodeEvPairs_encode {m : Nat} {es : List Event} (h : ItemsEv m es) (hm : m % 2 = 0) :
    ∀ f r, 2 * (encodeEvents es).length + 1 ≤ f →
      decodeEvPairsUntilBreak f (encodeEvents es ++ breakByte :: r) = some (es, r) := by
  intro f r hf
  match m, es, h, hm with
  | _, _, .nil, _ =>
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [decodeEvPairsUntilBreak, encodeEvents]
  | _, _, .cons _ .nil, hm => omega
  | _, _, .cons (es := es1) he (.cons (es := es2) (fs := fs) he2 hfs), hm =>
    have := encodeEvents_length_pos he
    have := encodeEvents_length_pos he2
    rw [encodeEvents_append, encodeEvents_append] at hf ⊢
    simp only [List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hs := decodeEv_encode he g (encodeEvents es2 ++ encodeEvents fs ++ breakByte :: r)
      (by omega)
    have ht := decodeEv_encode he2 g (encodeEvents fs ++ breakByte :: r) (by omega)
    have hrec := decodeEvPairs_encode hfs (by omega) g r (by omega)
    obtain ⟨b, t, hbt, hb⟩ := encodeEvents_head he
    rw [List.append_assoc, List.append_assoc, hbt, List.cons_append]
    rw [hbt, List.cons_append, List.append_assoc] at hs
    simp only [decodeEvPairsUntilBreak, hb, ↓reduceIte, hs, Option.bind_some, ht, hrec,
      Option.map_some, List.append_assoc]

end

theorem decodeEvents_encode {es : List Event} (h : ItemEv es) :
    decodeEvents (encodeEvents es) = some es := by
  have := decodeEv_encode h (2 * (encodeEvents es).length + 2) [] (by omega)
  rw [List.append_nil] at this
  simp [decodeEvents, this]

/-! ## Values -/

mutual

theorem encodeEvents_toEvents (v : Value) : encodeEvents v.toEvents = v.encode := by
  match v with
  | .uint _ | .nint _ | .bytes _ | .text _ | .simple _ | .float _ _ =>
    simp [Value.toEvents, Value.encode, encodeEvents, Event.encode]
  | .array xs =>
    rw [Value.toEvents, encodeEvents_append, encodeEvents_cons, encodeEvents_listEvents]
    simp [Value.encode, encodeEvents, Event.encode]
  | .map kvs =>
    rw [Value.toEvents, encodeEvents_append, encodeEvents_cons, encodeEvents_mapEvents]
    simp [Value.encode, encodeEvents, Event.encode]
  | .tag n w =>
    rw [Value.toEvents, encodeEvents_cons, encodeEvents_toEvents w]
    rfl

theorem encodeEvents_listEvents (xs : List Value) : encodeEvents (listEvents xs) = encodeList xs := by
  match xs with
  | [] => rfl
  | x :: xs =>
    rw [listEvents, encodeEvents_append, encodeEvents_toEvents, encodeEvents_listEvents xs]
    rfl

theorem encodeEvents_mapEvents (kvs : List (Value × Value)) :
    encodeEvents (mapEvents kvs) = encodeMap kvs := by
  match kvs with
  | [] => rfl
  | (k, v) :: kvs =>
    rw [mapEvents, encodeEvents_append, encodeEvents_append, encodeEvents_toEvents,
      encodeEvents_toEvents, encodeEvents_mapEvents kvs]
    simp [encodeMap]

end

mutual

theorem itemEv_toEvents (v : Value) (hv : v.Encodable) : ItemEv v.toEvents := by
  match v, hv with
  | .uint _, hv => exact .uint hv
  | .nint _, hv => exact .nint hv
  | .bytes _, hv => exact .bytes hv
  | .text _, hv => exact .text hv
  | .array xs, ⟨hl, hx⟩ => exact .array hl (itemsEv_listEvents xs hx)
  | .map kvs, ⟨hl, hx⟩ => exact .map hl (itemsEv_mapEvents kvs hx)
  | .tag _ w, ⟨ha, hw⟩ => exact .tag ha (itemEv_toEvents w hw)
  | .simple _, hv => exact .simple hv
  | .float _ _, ⟨hw, hb⟩ => exact .float hw hb

theorem itemsEv_listEvents (xs : List Value) (hx : ListEncodable xs) :
    ItemsEv xs.length (listEvents xs) := by
  match xs, hx with
  | [], _ => exact .nil
  | x :: xs, ⟨h1, h2⟩ => exact .cons (itemEv_toEvents x h1) (itemsEv_listEvents xs h2)

theorem itemsEv_mapEvents (kvs : List (Value × Value)) (hx : MapEncodable kvs) :
    ItemsEv (2 * kvs.length) (mapEvents kvs) := by
  match kvs, hx with
  | [], _ => exact .nil
  | (k, v) :: kvs, ⟨h1, h2, h3⟩ =>
    rw [List.length_cons, show 2 * (kvs.length + 1) = 2 * kvs.length + 1 + 1 by omega]
    simp only [mapEvents, List.append_assoc]
    exact .cons (itemEv_toEvents k h1) (.cons (itemEv_toEvents v h2) (itemsEv_mapEvents kvs h3))

end

/-! ## Payload bounds -/

theorem bounded_map_bytes {cs : List (List UInt8)} (h : ∀ c ∈ cs, c.length < 2 ^ 64) :
    ∀ e ∈ cs.map Event.bytes, e.Bounded := by
  intro e he
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  exact h c hc

theorem bounded_map_text {cs : List (List UInt8)} (h : ∀ c ∈ cs, c.length < 2 ^ 64) :
    ∀ e ∈ cs.map Event.text, e.Bounded := by
  intro e he
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  exact h c hc

mutual

theorem ItemEv.bounded {es : List Event} : ItemEv es → ∀ e ∈ es, e.Bounded
  | .uint h, e, he | .nint h, e, he | .bytes h, e, he | .text h, e, he | .simple h, e, he => by
    simp at he; subst he; exact h
  | .float hw hb, e, he => by simp at he; subst he; exact ⟨hw, hb⟩
  | .indefBytes h, e, he => by
    simp only [List.cons_append, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | he | rfl
    · trivial
    · exact bounded_map_bytes h e he
    · trivial
  | .indefText h, e, he => by
    simp only [List.cons_append, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | he | rfl
    · trivial
    · exact bounded_map_text h e he
    · trivial
  | .array h hx, e, he | .map h hx, e, he => by
    simp only [List.cons_append, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | he | rfl
    · exact h
    · exact ItemsEv.bounded hx e he
    · exact h
  | .indefArray hx, e, he | .indefMap hx, e, he => by
    simp only [List.cons_append, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | he | rfl
    · trivial
    · exact ItemsEv.bounded hx e he
    · trivial
  | .tag h hx, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact h
    · exact ItemEv.bounded hx e he

theorem ItemsEv.bounded {k : Nat} {es : List Event} : ItemsEv k es → ∀ e ∈ es, e.Bounded
  | .nil, _, he => by simp at he
  | .cons h1 h2, e, he => by
    rcases List.mem_append.mp he with he | he
    · exact ItemEv.bounded h1 e he
    · exact ItemsEv.bounded h2 e he

end

end Silmaril.Proofs.Formats.Cbor.Events

end
