module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules

/-!
# Proofs: decoding payload values through memory

* `le32_encode`, `readPtrLen_encode`: a `(ptr, len)` pair written as two little-endian `i32`s
  is read back;
* `readPtrLen_rest`, `readVal_rest` (with `rest_of_map`, `rest_of_bind_map`): **a payload
  value consumes exactly `PTy.width t` bytes** (its canonical ABI element size), for every
  payload type;
* `readVal_string`, `readVal_bytes` (with `readMany_u8`), `readVal_list`: the indirect values
  from their pair, the memory segment it names and (for strings) its UTF-8 decoding, (for
  lists) its alignment and its elements; `readVal_list_misaligned`: a misaligned list is no
  value;
* `alignTo_zero`, `readVals_single`: a one-value payload vector;
* `layout_toWit` (mutually with `layoutTypes_toWitList`, `layoutFields_toWit`,
  `layoutCases_toWit`, `layoutOption_toWit`), `layoutTypes_toWit`, `valsLayout_toWit`: **the
  layouts are the canonical ABI layouts** `ABI.layout .i32` of the WIT types `Wit.toWit t`
  (records, tuples, variants, options, results, enums, flags and fixed-length lists included)
  and of the tuple of `Wit.toWitList ps`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Formats Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Component
open Silmaril.Wasm.Game.HandleAccept.Wit (toWit toWitList toWitFields toWitCases toWitOpt)

theorem length_encode4 (v : Nat) : (Memory.encodeLE 4 v).data.toList.length = 4 := by
  rw [Array.length_toList]
  exact Memory.encodeLE_size 4 v

theorem le32_encode (r : BitVec 32) : le32 (Memory.encodeLE 4 r.toNat).data.toList = some r := by
  unfold le32
  rw [← List.append_nil (Memory.encodeLE 4 r.toNat).data.toList, le32s_encode]
  rfl

/-- **A `(ptr, len)` pair is read back.** -/
theorem readPtrLen_encode (p n : BitVec 32) (rest : List UInt8) :
    readPtrLen ((Memory.encodeLE 4 p.toNat).data.toList ++ (Memory.encodeLE 4 n.toNat).data.toList
      ++ rest) = some (p.toNat, n.toNat, rest) := by
  have hp := length_encode4 p.toNat
  have hn := length_encode4 n.toNat
  unfold readPtrLen
  rw [List.append_assoc, List.take_left' hp, le32_encode, List.drop_left' hp,
    List.take_left' hn, le32_encode]
  simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
  rw [show 8 = 4 + 4 from rfl, ← List.drop_drop, List.drop_left' hp, List.drop_left' hn]

/-- A pair leaves the payload area after its eight bytes. -/
theorem readPtrLen_rest {bs rest : List UInt8} {p n : Nat}
    (h : readPtrLen bs = some (p, n, rest)) : rest = bs.drop 8 := by
  unfold readPtrLen at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨_, -, _, -, -, -, rfl⟩ := h
  rfl

/-- A value read by `Option.map` into `(v, bs.drop w)` leaves `bs.drop w`. -/
theorem rest_of_map {α β : Type} {x : Option α} {f : α → β} {bs rest : List UInt8} {w : Nat}
    {v : β} (h : x.map (fun a => (f a, bs.drop w)) = some (v, rest)) : rest = bs.drop w := by
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨_, -, h⟩ := h
  exact (congrArg Prod.snd h).symm

/-- A value read by `Option.bind` then `Option.map` into `(v, bs.drop w)` leaves `bs.drop w`. -/
theorem rest_of_bind_map {α β γ : Type} {x : Option α} {g : α → Option β} {f : β → γ}
    {bs rest : List UInt8} {w : Nat} {v : γ}
    (h : x.bind (fun a => (g a).map fun b => (f b, bs.drop w)) = some (v, rest)) :
    rest = bs.drop w := by
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, h⟩ := h
  exact (congrArg Prod.snd h).symm

/-- **A payload value consumes exactly its width.** -/
theorem readVal_rest {seg : Nat → Nat → Option (List UInt8)} :
    ∀ {t : PTy} {bs rest : List UInt8} {v : t.Val},
      readVal seg t bs = some (v, rest) → rest = bs.drop (PTy.width t)
  | .bool, b :: bs, rest, v, h => by
    simp only [readVal] at h
    exact (congrArg Prod.snd (Option.some.inj h)).symm
  | .bool, [], _, _, h => by simp [readVal] at h
  | .u8, b :: bs, rest, v, h => by
    simp only [readVal] at h
    exact (congrArg Prod.snd (Option.some.inj h)).symm
  | .u8, [], _, _, h => by simp [readVal] at h
  | .own _, _, _, _, h | .borrow _, _, _, _, h => by simp [readVal] at h
  | .s32, _, _, _, h | .u32, _, _, _, h | .s64, _, _, _, h | .u64, _, _, _, h
  | .s8, _, _, _, h | .s16, _, _, _, h | .u16, _, _, _, h | .f32, _, _, _, h
  | .f64, _, _, _, h | .record _, _, _, _, h | .tuple _, _, _, _, h | .flags _, _, _, _, h =>
    rest_of_map h
  | .char, _, _, _, h | .fixedList _ _, _, _, _, h | .variant _, _, _, _, h
  | .enum _, _, _, _, h | .option _, _, _, _, h | .result _ _, _, _, _, h =>
    rest_of_bind_map h
  | .string, bs, rest, v, h => by
    rcases hp : readPtrLen bs with _ | ⟨p, n, r⟩
    · simp [readVal, hp] at h
    · simp only [readVal, hp, Option.bind_some] at h
      rcases hc : seg p n with _ | cs
      · simp [hc] at h
      · rcases hu : utf8? cs with _ | str
        · simp only [hc, hu, Option.bind_some] at h
          cases h
        · simp only [hc, hu, Option.bind_some] at h
          have e : r = rest := congrArg Prod.snd (Option.some.inj h)
          rw [← e]; exact readPtrLen_rest hp
  | .list t, bs, rest, v, h => by
    rcases hp : readPtrLen bs with _ | ⟨p, n, r⟩
    · simp [readVal, hp] at h
    · simp only [readVal, hp, Option.bind_some] at h
      split at h
      · rcases hc : seg p (n * PTy.width t) with _ | es
        · simp [hc] at h
        · simp only [hc, Option.bind_some] at h
          rcases hm : readMany (readVal seg t) n es with _ | ⟨vs, r'⟩
          · simp [hm] at h
          · simp only [hm, Option.bind_some] at h
            split at h
            · have e : r = rest := congrArg Prod.snd (Option.some.inj h)
              rw [← e]; exact readPtrLen_rest hp
            · cases h
      · cases h

/-- **A string payload**: its pair, the segment it names, the UTF-8 text. -/
theorem readVal_string {seg : Nat → Nat → Option (List UInt8)} {bs rest cs : List UInt8}
    {p n : Nat} {str : String} (hp : readPtrLen bs = some (p, n, rest))
    (hc : seg p n = some cs) (hu : utf8? cs = some str) :
    readVal seg .string bs = some (str, rest) := by
  simp only [readVal, hp, Option.bind_some, hc, hu]
  rfl

/-- `n` bytes read as `u8`s are themselves. -/
theorem readMany_u8 (seg : Nat → Nat → Option (List UInt8)) :
    ∀ cs : List UInt8, readMany (readVal seg .u8) cs.length cs = some (cs, [])
  | [] => rfl
  | c :: cs => by
    simp only [List.length_cons, readMany, readVal, Option.bind_some, readMany_u8 seg cs]
    rfl

/-- **A byte-string payload** (`list<u8>`): its pair and the `len` bytes it names. -/
theorem readVal_bytes {seg : Nat → Nat → Option (List UInt8)} {bs rest cs : List UInt8}
    {p n : Nat} (hp : readPtrLen bs = some (p, n, rest)) (hc : seg p n = some cs)
    (hl : cs.length = n) :
    readVal seg .bytes bs = some (cs, rest) := by
  subst hl
  have hc' : seg p (cs.length * PTy.width .u8) = some cs := by
    simpa [PTy.width, PTy.layout, ABI.Layout.size, ABI.Alignment.bytes] using hc
  simp only [readVal, hp, Option.bind_some, show p % PTy.align .u8 = 0 from Nat.mod_one p,
    ↓reduceIte, hc', readMany_u8]
  rfl

/-- **A list payload**: its pair, the segment of `len` packed elements, the elements. -/
theorem readVal_list {seg : Nat → Nat → Option (List UInt8)} {t : PTy}
    {bs rest es : List UInt8} {p n : Nat} {vs : List t.Val}
    (hp : readPtrLen bs = some (p, n, rest)) (ha : p % PTy.align t = 0)
    (hc : seg p (n * PTy.width t) = some es)
    (hm : readMany (readVal seg t) n es = some (vs, [])) :
    readVal seg (.list t) bs = some (vs, rest) := by
  simp only [readVal, hp, Option.bind_some, ha, ↓reduceIte, hc, hm, List.isEmpty_nil]
  rfl

/-- **A misaligned list is no value** (REF `trap_if(ptr != align_to(ptr, alignment))`). -/
theorem readVal_list_misaligned {seg : Nat → Nat → Option (List UInt8)} {t : PTy}
    {bs rest : List UInt8} {p n : Nat} (hp : readPtrLen bs = some (p, n, rest))
    (ha : p % PTy.align t ≠ 0) : readVal seg (.list t) bs = none := by
  simp [readVal, hp, ha]

/-- A field at offset `0` is not padded. -/
theorem alignTo_zero (a : ABI.Alignment) : ABI.alignTo 0 a = 0 := by
  cases a <;> rfl

/-- **A one-value payload vector** is its value, read from the first `t.width` bytes. -/
theorem readVals_single (seg : Nat → Nat → Option (List UInt8)) (t : PTy) (area : List UInt8) :
    readVals seg [t] area =
      (readVal seg t (area.take (PTy.width t))).map fun (v, _) => (v, ()) := by
  simp only [readVals, readFields, alignTo_zero, List.drop_zero]
  cases readVal seg t (area.take (PTy.width t)) <;> rfl

/-! ## Agreement with the canonical ABI layout -/

section Layout

mutual
/-- **The layout of a payload type is its canonical ABI layout** (memory32). -/
theorem layout_toWit : ∀ t : PTy,
    ABI.layout .i32 (toWit t : WIT.ClosedType Nat) = PTy.layout t
  | .bool | .s32 | .u32 | .s64 | .u64 | .string | .s8 | .u8 | .s16 | .u16 | .f32 | .f64
  | .char | .enum _ | .flags _ | .own _ | .borrow _ => by
    simp only [toWit, ABI.layout, PTy.layout, ABI.primitiveLayout]
  | .list _ => by simp only [toWit, ABI.layout, PTy.layout]
  | .fixedList t _ => by simp only [toWit, ABI.layout, PTy.layout, layout_toWit t]
  | .option t => by simp only [toWit, ABI.layout, PTy.layout, layout_toWit t]
  | .record fs => by simp only [toWit, ABI.layout, PTy.layout, layoutFields_toWit fs]
  | .tuple ts => by simp only [toWit, ABI.layout, PTy.layout, layoutTypes_toWitList ts]
  | .variant cs => by simp only [toWit, ABI.layout, PTy.layout, layoutCases_toWit cs]
  | .result ok err => by
    simp only [toWit, ABI.layout, PTy.layout, layoutOption_toWit ok, layoutOption_toWit err]

theorem layoutTypes_toWitList : ∀ ts : List PTy,
    ABI.layoutTypes .i32 (toWitList ts : List (WIT.ClosedType Nat)) = PTy.layouts ts
  | [] => by simp only [toWitList, ABI.layoutTypes, PTy.layouts]
  | t :: ts => by
    simp only [toWitList, ABI.layoutTypes, PTy.layouts, layout_toWit t, layoutTypes_toWitList ts]

theorem layoutFields_toWit : ∀ fs : List (String × PTy),
    ABI.layoutFields .i32 (toWitFields fs : List (String × WIT.ClosedType Nat)) =
      PTy.fieldLayouts fs
  | [] => by simp only [toWitFields, ABI.layoutFields, PTy.fieldLayouts]
  | (_, t) :: fs => by
    simp only [toWitFields, ABI.layoutFields, PTy.fieldLayouts, layout_toWit t,
      layoutFields_toWit fs]

theorem layoutCases_toWit : ∀ cs : List (String × Option PTy),
    ABI.layoutCases .i32 (toWitCases cs : List (String × Option (WIT.ClosedType Nat))) =
      PTy.caseLayouts cs
  | [] => by simp only [toWitCases, ABI.layoutCases, PTy.caseLayouts]
  | (_, o) :: cs => by
    simp only [toWitCases, ABI.layoutCases, PTy.caseLayouts, layoutOption_toWit o,
      layoutCases_toWit cs]

theorem layoutOption_toWit : ∀ o : Option PTy,
    ABI.layoutOption .i32 (toWitOpt o : Option (WIT.ClosedType Nat)) = PTy.optLayout o
  | none => by simp only [toWitOpt, ABI.layoutOption, PTy.optLayout]
  | some t => by simp only [toWitOpt, ABI.layoutOption, PTy.optLayout, layout_toWit t]
end

/-- `PTy.layouts` is `List.map PTy.layout`. -/
theorem layouts_eq_map : ∀ ps : List PTy, PTy.layouts ps = ps.map PTy.layout
  | [] => rfl
  | t :: ps => by rw [PTy.layouts, layouts_eq_map ps, List.map_cons]

theorem layoutTypes_toWit (ps : List PTy) :
    ABI.layoutTypes .i32 (toWitList ps : List (WIT.ClosedType Nat)) =
      ps.map PTy.layout := by
  rw [layoutTypes_toWitList, layouts_eq_map]

/-- **The layout of a payload vector is the canonical ABI layout of its tuple.** -/
theorem valsLayout_toWit (ps : List PTy) :
    ABI.layout .i32 (.tuple (toWitList ps) : WIT.ClosedType Nat) = valsLayout ps := by
  rw [ABI.layout, layoutTypes_toWit]
  rfl

end Layout

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst
