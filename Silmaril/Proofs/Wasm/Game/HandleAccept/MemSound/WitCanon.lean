module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Canon.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitPayload

/-!
# Proofs: payload decoding against the pure canonical ABI reference loaders

* `le32_eq`, `le64_eq`, `load_eq`: the little-endian words of the decoder are the reference
  `Execution.Memory.load` (`decodeLE`) words;
* `readVal_scalar`: a scalar payload value read from its bytes is the reference scalar
  (`ABI.Scalar.load`, `Scalar.liftBits`);
* `alignTo_add`, `le_alignTo`, `le_recordEnd`, `dvd_recordAlignment`: record layout arithmetic;
* `readFields_loadFields`, `loadVals_loadRecord`: **scalar payload vectors are
  `ABI.loadRecord`**, failures included;
* `readPtrLen_load`: a `(ptr, len)` pair is the two reference `u32` loads;
* `readVal_string_loadStringFromRange`: **a string payload is `ABI.loadStringFromRange?`**
  (UTF-8, memory32) below `ABI.maxStringByteLength`, and the reference fails above it.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Formats Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Component
open Silmaril.Wasm.Logic.Core (bytesAt leNat)

/-! ## Words -/

theorem le32_eq : ∀ (l : List UInt8), l.length = 4 → le32 l = some (BitVec.ofNat 32 (leNat l))
  | [a, b, c, d], _ => by
    simp only [le32, le32s, Option.map_some, leNat, List.foldr]
    congr 2
    omega

theorem le64_eq : ∀ (l : List UInt8), l.length = 8 → le64 l = some (BitVec.ofNat 64 (leNat l))
  | [b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇], _ => by
    simp only [le64, leNat, List.foldr]
    congr 2
    omega

theorem decodeLE_eq (bs : ByteArray) : Memory.decodeLE bs = leNat bs.data.toList := by
  simp only [Memory.decodeLE, leNat, ← Array.foldr_toList]

theorem segOf_of_le {mem : ByteArray} {a n : Nat} (h : a + n ≤ mem.size) :
    segOf mem a n = some (bytesAt mem ⟨a, n⟩) :=
  readBytes_toList h

theorem segOf_of_lt {mem : ByteArray} {a n : Nat} (h : mem.size < a + n) : segOf mem a n = none := by
  simp only [segOf, Memory.readBytes, show ¬(a + n ≤ mem.size) by omega, ↓reduceIte,
    Option.map_none]

theorem length_bytesAt {mem : ByteArray} {a n : Nat} (h : a + n ≤ mem.size) :
    (bytesAt mem ⟨a, n⟩).length = n := by
  simp only [bytesAt, List.length_take, List.length_drop, Array.length_toList]
  have : mem.data.size = mem.size := rfl
  omega

theorem load_eq (mem : ByteArray) (a n : Nat) :
    Memory.load mem a n = (segOf mem a n).map fun l => BitVec.ofNat (8 * n) (leNat l) := by
  simp only [Memory.load, segOf, Option.map_map]
  congr 1
  funext bs
  simp only [Function.comp_apply, decodeLE_eq]

theorem bytesAt_sub {mem : ByteArray} {s W off w : Nat} (h : off + w ≤ W) :
    ((bytesAt mem ⟨s, W⟩).drop off).take w = bytesAt mem ⟨s + off, w⟩ := by
  simp only [bytesAt, List.drop_take, List.drop_drop, List.take_take]
  congr 1
  omega

/-! ## Scalars -/

theorem width_pty (q : SPTy) : PTy.width q.pty = q.scalar.byteCount := by
  cases q <;> rfl

theorem layout_pty (q : SPTy) :
    PTy.layout q.pty = ABI.primitiveLayout .i32 q.scalar.primitive := by
  cases q <;> rfl

theorem alignment_pty (q : SPTy) : (PTy.layout q.pty).alignment = q.scalar.alignment := by
  cases q <;> rfl

theorem toNat_ofNat_byte (b : UInt8) : (BitVec.ofNat 8 b.toNat) = 0 ↔ b = 0 := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt b)] at h'
    exact UInt8.toNat_inj.mp (by simpa using h')
  · rintro rfl; rfl

theorem bool_bits (b : UInt8) :
    (if (b != 0) = true then (1 : BitVec 1) else 0) =
      BitVec.ofNat 1 (if BitVec.ofNat 8 (leNat [b]) = 0 then 0 else 1) := by
  by_cases hb : b = 0
  · subst hb; rfl
  · have h2 : ¬ BitVec.ofNat 8 (leNat [b]) = 0 := by
      simp only [leNat, List.foldr, Nat.mul_zero, Nat.add_zero]
      exact fun h => hb ((toNat_ofNat_byte b).mp h)
    have h1 : (b != 0) = true := by simpa using hb
    simp only [h1, h2, ↓reduceIte]
    rfl

theorem scalarValue_congr {t : ABI.Scalar} {a b : BitVec t.width} (h : a = b) :
    (⟨t, a⟩ : ABI.ScalarValue) = ⟨t, b⟩ := h ▸ rfl

/-- **A scalar payload value** read from exactly its bytes is the reference scalar. -/
theorem readVal_scalar (seg : Nat → Nat → Option (List UInt8)) (q : SPTy) (l : List UInt8)
    (hl : l.length = q.scalar.byteCount) :
    ∃ v, readVal seg q.pty l = some (v, []) ∧
      q.toScalarValue v =
        ⟨q.scalar, q.scalar.liftBits (BitVec.ofNat (8 * q.scalar.byteCount) (leNat l))⟩ := by
  cases q
  · match l, hl with
    | [b], _ =>
      refine ⟨b != 0, rfl, ?_⟩
      apply scalarValue_congr
      exact bool_bits b
  · simp only [SPTy.scalar, ABI.Scalar.byteCount] at hl
    refine ⟨Int32.ofBitVec (BitVec.ofNat 32 (leNat l)), ?_, ?_⟩
    · simp only [SPTy.pty, readVal, List.take_of_length_le (Nat.le_of_eq hl), le32_eq l hl,
        Option.map_some, List.drop_eq_nil_of_le (Nat.le_of_eq hl)]
    · apply scalarValue_congr
      simp only [SPTy.scalar, Int32.toBitVec_ofBitVec, ABI.Scalar.liftBits,
        reduceCtorEq, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, ABI.Scalar.width, ABI.Scalar.byteCount]
  · simp only [SPTy.scalar, ABI.Scalar.byteCount] at hl
    refine ⟨UInt32.ofBitVec (BitVec.ofNat 32 (leNat l)), ?_, ?_⟩
    · simp only [SPTy.pty, readVal, List.take_of_length_le (Nat.le_of_eq hl), le32_eq l hl,
        Option.map_some, List.drop_eq_nil_of_le (Nat.le_of_eq hl)]
    · apply scalarValue_congr
      simp only [SPTy.scalar, ABI.Scalar.liftBits,
        reduceCtorEq, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, ABI.Scalar.width, ABI.Scalar.byteCount]
  · simp only [SPTy.scalar, ABI.Scalar.byteCount] at hl
    refine ⟨Int64.ofBitVec (BitVec.ofNat 64 (leNat l)), ?_, ?_⟩
    · simp only [SPTy.pty, readVal, List.take_of_length_le (Nat.le_of_eq hl), le64_eq l hl,
        Option.map_some, List.drop_eq_nil_of_le (Nat.le_of_eq hl)]
    · apply scalarValue_congr
      simp only [SPTy.scalar, Int64.toBitVec_ofBitVec, ABI.Scalar.liftBits,
        reduceCtorEq, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, ABI.Scalar.width, ABI.Scalar.byteCount]
  · simp only [SPTy.scalar, ABI.Scalar.byteCount] at hl
    refine ⟨UInt64.ofBitVec (BitVec.ofNat 64 (leNat l)), ?_, ?_⟩
    · simp only [SPTy.pty, readVal, List.take_of_length_le (Nat.le_of_eq hl), le64_eq l hl,
        Option.map_some, List.drop_eq_nil_of_le (Nat.le_of_eq hl)]
    · apply scalarValue_congr
      simp only [SPTy.scalar, ABI.Scalar.liftBits,
        reduceCtorEq, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, ABI.Scalar.width, ABI.Scalar.byteCount]

/-! ## Record layout arithmetic -/

theorem alignTo_add {a : ABI.Alignment} {s : Nat} (h : s % a.bytes = 0) (c : Nat) :
    ABI.alignTo (s + c) a = s + ABI.alignTo c a := by
  cases a <;> simp only [ABI.alignTo, ABI.Alignment.bytes] at h ⊢ <;> omega

theorem le_alignTo (c : Nat) (a : ABI.Alignment) : c ≤ ABI.alignTo c a := by
  cases a <;> simp only [ABI.alignTo, ABI.Alignment.bytes] <;> omega

theorem le_recordEnd : ∀ (c : Nat) (ls : List ABI.Layout), c ≤ ABI.recordEnd c ls
  | _, [] => Nat.le_refl _
  | c, l :: ls => by
    have h1 := le_alignTo c l.alignment
    have h2 := le_recordEnd (ABI.placeField c l).2 ls
    simp only [ABI.recordEnd, ABI.placeField] at h2 ⊢
    omega

theorem dvd_join_left (a b : ABI.Alignment) : a.bytes ∣ (a.join b).bytes := by
  cases a <;> cases b <;> decide

theorem dvd_join_right (a b : ABI.Alignment) : b.bytes ∣ (a.join b).bytes := by
  cases a <;> cases b <;> decide

theorem dvd_recordAlignment : ∀ {ls : List ABI.Layout} {l : ABI.Layout}, l ∈ ls →
    l.alignment.bytes ∣ (ABI.recordAlignment ls).bytes
  | l' :: ls, l, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact dvd_join_left _ _
    · exact Nat.dvd_trans (dvd_recordAlignment h) (dvd_join_right _ _)

theorem scalarRecordLayout_eq (qs : List SPTy) :
    ABI.scalarRecordLayout (qs.map SPTy.scalar) = valsLayout (qs.map SPTy.pty) := by
  simp only [ABI.scalarRecordLayout, valsLayout, List.map_map]
  congr 1
  exact List.map_congr_left fun q _ => (layout_pty q).symm

/-! ## Scalar records -/

theorem readFields_cons_map (seg : Nat → Nat → Option (List UInt8)) (q : SPTy) (qs : List SPTy)
    (cur : Nat) (area : List UInt8) :
    (readFields seg ((q :: qs).map SPTy.pty) cur area).map (SPTy.toScalarValues (q :: qs)) =
      (readVal seg q.pty ((area.drop (ABI.alignTo cur (PTy.layout q.pty).alignment)).take
          (PTy.width q.pty))).bind fun x =>
        (readFields seg (qs.map SPTy.pty)
          (ABI.alignTo cur (PTy.layout q.pty).alignment + PTy.width q.pty) area).map fun vs =>
            q.toScalarValue x.1 :: SPTy.toScalarValues qs vs := by
  show Option.map _ ((readVal seg q.pty _).bind _) = _
  rcases readVal seg q.pty ((area.drop (ABI.alignTo cur (PTy.layout q.pty).alignment)).take
      (PTy.width q.pty)) with _ | ⟨v, r⟩
  · rfl
  · simp only [Option.bind_some]
    cases readFields seg (qs.map SPTy.pty)
      (ABI.alignTo cur (PTy.layout q.pty).alignment + PTy.width q.pty) area <;> rfl

theorem readFields_loadFields (mem : ByteArray) (start W : Nat) (hW : start + W ≤ mem.size) :
    ∀ (qs : List SPTy) (cur : Nat),
      (∀ q ∈ qs, start % q.scalar.alignment.bytes = 0) →
      ABI.recordEnd cur ((qs.map SPTy.pty).map PTy.layout) ≤ W →
      (readFields (segOf mem) (qs.map SPTy.pty) cur (bytesAt mem ⟨start, W⟩)).map
          (SPTy.toScalarValues qs) =
        ABI.loadFields mem (start + cur) (qs.map SPTy.scalar)
  | [], _, _, _ => rfl
  | q :: qs, cur, hA, hE => by
    have hq := hA q List.mem_cons_self
    have hrest : ∀ q' ∈ qs, start % q'.scalar.alignment.bytes = 0 :=
      fun q' h => hA q' (List.mem_cons_of_mem _ h)
    simp only [List.map_cons, ABI.recordEnd, ABI.placeField] at hE
    rw [alignment_pty] at hE
    have hw : (PTy.layout q.pty).size = q.scalar.byteCount := width_pty q
    rw [hw] at hE
    have hEnd := le_recordEnd (ABI.alignTo cur q.scalar.alignment + q.scalar.byteCount)
      ((qs.map SPTy.pty).map PTy.layout)
    have ih := readFields_loadFields mem start W hW qs
      (ABI.alignTo cur q.scalar.alignment + q.scalar.byteCount) hrest hE
    have hb : start + ABI.alignTo cur q.scalar.alignment + q.scalar.byteCount ≤ mem.size := by
      omega
    obtain ⟨v, hv, hsv⟩ := readVal_scalar (segOf mem) q
      (bytesAt mem ⟨start + ABI.alignTo cur q.scalar.alignment, q.scalar.byteCount⟩)
      (length_bytesAt hb)
    refine (readFields_cons_map (segOf mem) q qs cur _).trans ?_
    rw [alignment_pty, width_pty,
      bytesAt_sub (show ABI.alignTo cur q.scalar.alignment + q.scalar.byteCount ≤ W by omega), hv,
      Option.bind_some]
    have hl : ABI.Scalar.load q.scalar mem (start + ABI.alignTo cur q.scalar.alignment) =
        some (q.toScalarValue v) := by
      rw [hsv, ABI.Scalar.load, load_eq, segOf_of_le hb]
      rfl
    simp only [List.map_cons, ABI.loadFields, alignTo_add hq, hl]
    rw [Nat.add_assoc, ← ih]
    cases readFields (segOf mem) (qs.map SPTy.pty)
      (ABI.alignTo cur q.scalar.alignment + q.scalar.byteCount) (bytesAt mem ⟨start, W⟩) <;> rfl

/-- **Scalar payload vectors are `ABI.loadRecord`.** -/
theorem loadVals_loadRecord (mem : ByteArray) (qs : List SPTy) (ptr : Nat) :
    (loadVals mem (qs.map SPTy.pty) ptr).map (SPTy.toScalarValues qs) =
      ABI.loadRecord (qs.map SPTy.scalar) mem ptr := by
  have hl := scalarRecordLayout_eq qs
  unfold loadVals ABI.loadRecord
  simp only [hl]
  by_cases ha : ptr % valsAlign (qs.map SPTy.pty) = 0
  · have ha' : ptr % (valsLayout (qs.map SPTy.pty)).alignment.bytes = 0 := ha
    by_cases hb : ptr + valsWidth (qs.map SPTy.pty) ≤ mem.size
    · have hb' : ptr + (valsLayout (qs.map SPTy.pty)).size ≤ mem.size := hb
      simp only [ha, ha', hb', and_self, ↓reduceIte, segOf_of_le hb, Option.bind_some, readVals]
      refine readFields_loadFields mem ptr _ hb _ 0 (fun q hq => ?_) ?_
      · have hd : q.scalar.alignment.bytes ∣ (valsLayout (qs.map SPTy.pty)).alignment.bytes := by
          rw [← alignment_pty]
          exact dvd_recordAlignment (List.mem_map.mpr ⟨q.pty, List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩)
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd (Nat.dvd_of_mod_eq_zero ha'))
      · exact le_alignTo _ _
    · have hb' : ¬ ptr + (valsLayout (qs.map SPTy.pty)).size ≤ mem.size := hb
      simp only [ha, hb', and_false, ↓reduceIte, segOf_of_lt (Nat.lt_of_not_le hb),
        Option.bind_none, Option.map_none]
  · have ha' : ¬ ptr % (valsLayout (qs.map SPTy.pty)).alignment.bytes = 0 := ha
    simp only [ha, ha', false_and, ↓reduceIte, Option.map_none]

theorem toScalarValue_injective : ∀ q : SPTy, Function.Injective q.toScalarValue
  | .bool, a, b, h => by
    cases a <;> cases b <;> first
      | rfl
      | exact absurd (congrArg (fun x : ABI.ScalarValue => x.bits.toNat) h) (by decide)
  | .s32, a, b, h => by
    have h := congrArg (fun x : ABI.ScalarValue => x.bits.toNat) h
    simp only [SPTy.toScalarValue] at h
    exact Int32.toBitVec_inj.mp (BitVec.eq_of_toNat_eq h)
  | .u32, a, b, h => by
    have h := congrArg (fun x : ABI.ScalarValue => x.bits.toNat) h
    simp only [SPTy.toScalarValue] at h
    exact UInt32.toBitVec_inj.mp (BitVec.eq_of_toNat_eq h)
  | .s64, a, b, h => by
    have h := congrArg (fun x : ABI.ScalarValue => x.bits.toNat) h
    simp only [SPTy.toScalarValue] at h
    exact Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq h)
  | .u64, a, b, h => by
    have h := congrArg (fun x : ABI.ScalarValue => x.bits.toNat) h
    simp only [SPTy.toScalarValue] at h
    exact UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq h)

theorem toScalarValues_injective : ∀ qs : List SPTy, Function.Injective (SPTy.toScalarValues qs)
  | [], _, _, _ => rfl
  | q :: qs, a, b, h => by
    simp only [SPTy.toScalarValues, List.cons.injEq] at h
    exact Prod.ext (toScalarValue_injective q h.1) (toScalarValues_injective qs h.2)

/-! ## Strings -/

/-- **A `(ptr, len)` pair is the two reference `u32` loads.** -/
theorem readPtrLen_load (mem : ByteArray) (a : Nat) :
    (segOf mem a 8).bind readPtrLen =
      (ABI.Scalar.load .u32 mem a).bind fun p =>
        (ABI.Scalar.load .u32 mem (a + 4)).map fun n => (p.bits.toNat, n.bits.toNat, []) := by
  simp only [ABI.Scalar.load, load_eq, ABI.Scalar.byteCount]
  by_cases hb : a + 8 ≤ mem.size
  · rw [segOf_of_le hb, segOf_of_le (show a + 4 ≤ mem.size by omega),
      segOf_of_le (show a + 4 + 4 ≤ mem.size by omega)]
    have hl := length_bytesAt hb
    have e1 : (bytesAt mem ⟨a, 8⟩).take 4 = bytesAt mem ⟨a, 4⟩ := by
      simpa using bytesAt_sub (mem := mem) (s := a) (off := 0) (w := 4) (W := 8) (by omega)
    have e2 : ((bytesAt mem ⟨a, 8⟩).drop 4).take 4 = bytesAt mem ⟨a + 4, 4⟩ :=
      bytesAt_sub (by omega)
    have h4 := length_bytesAt (show a + 4 ≤ mem.size by omega)
    have h4' := length_bytesAt (show a + 4 + 4 ≤ mem.size by omega)
    simp only [Option.bind_some, Option.map_some, readPtrLen, e1, e2, le32_eq _ h4,
      le32_eq _ h4', List.drop_eq_nil_of_le (Nat.le_of_eq hl)]
    simp [ABI.Scalar.liftBits, BitVec.toNat_ofNat, ABI.Scalar.width]
  · rw [segOf_of_lt (by omega), segOf_of_lt (show mem.size < a + 4 + 4 by omega)]
    cases segOf mem a 4 <;> rfl

/-- **A string payload is `ABI.loadStringFromRange?`** (UTF-8, memory32): below
`maxStringByteLength`, the same text or the same failure; above it, the reference fails. -/
theorem readVal_string_loadStringFromRange (mem : ByteArray) {bs rest : List UInt8} {p n : Nat}
    (hp : readPtrLen bs = some (p, n, rest)) :
    (ABI.loadStringFromRange? .utf8 .i32 mem.data.toList p n).map (fun v => (v, rest)) =
      if n ≤ ABI.maxStringByteLength then
        (readVal (segOf mem) .string bs).map fun x => (⟨x.1, .utf8, n⟩, x.2)
      else none := by
  have hsz : mem.data.toList.length = mem.size := Array.length_toList
  simp only [ABI.loadStringFromRange?, ABI.loadRange, readVal, hp, Option.bind_some, hsz,
    ABI.alignTo, ABI.Alignment.bytes, Nat.add_sub_cancel, Nat.div_one, Nat.mul_one, ne_eq,
    not_true_eq_false, ↓reduceIte, gt_iff_lt]
  by_cases hn : n ≤ ABI.maxStringByteLength
  · simp only [show ¬ ABI.maxStringByteLength < n by omega, ↓reduceIte, hn]
    by_cases hb : p + n ≤ mem.size
    · simp only [show ¬ mem.size < p + n by omega, ↓reduceIte, segOf_of_le hb, Option.bind_some,
        Option.map_map]
      cases h : utf8? (bytesAt mem ⟨p, n⟩) <;>
        simp_all [ABI.Codec.decode?, ABI.utf8Decode?, utf8?, bytesAt] <;>
        first | rfl | exact ⟨_, rfl, rfl⟩
    · simp only [show mem.size < p + n by omega, ↓reduceIte, segOf_of_lt (Nat.lt_of_not_le hb),
        Option.bind_none, Option.map_none]
  · simp only [show ABI.maxStringByteLength < n by omega, ↓reduceIte, hn, Option.map_none]

/-! ## The decoder of `node` -/

theorem segment_eq_segOf {o : Game.Accept.Callout} {mem : ByteArray} (hm : o.mem = some mem) :
    o.segment = segOf mem := by
  funext a n
  simp only [Game.Accept.Callout.segment, hm, segOf, Option.bind_eq_bind, Option.bind_some]

theorem witNode_loadVals (S : WitSig) (tagOf : BitVec 32 → Option S.Tag) {o : Game.Accept.Callout}
    {mem : ByteArray} (hm : o.mem = some mem) {op : Σ t, S.toAstSig.Arg t}
    {hs : List (BitVec 32)} (h : Callout.witNode S tagOf o = some (op, hs)) :
    ∃ pp : BitVec 32, o.args[1]? = some (Execution.Core.Val.i32 pp) ∧
      loadVals mem (S.params op.1) pp.toNat = some op.2 := by
  unfold Callout.witNode at h
  split at h
  next tg pp cp n heq =>
    obtain ⟨t, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · rename_i hal
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨bs, hbs, a, ha, cs, -, hs', -, h⟩ := h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨pp, by rw [heq]; rfl, ?_⟩
        rw [segment_eq_segOf hm] at hbs ha
        show loadVals mem (S.params t) pp.toNat = some a
        simp only [loadVals, hal.1, ↓reduceIte, hbs, Option.bind_some, ha]
      · cases h
    · cases h
  · cases h

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst
