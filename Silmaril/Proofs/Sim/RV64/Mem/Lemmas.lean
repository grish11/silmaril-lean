module

public import Silmaril.Sim.RV64.Mem.Defs
public import Silmaril.Wasm.Logic.VCTotal.Thms
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Logic.Memory.Thms

/-!
# The memory-state RV64 simulator: lemmas for its verification conditions

* Wasm evaluation: `memq` (memory `0` of the frame), `load8`/`load4` (a load is `ld64`/`ld32`
  when in bounds), `ib_*` (integer binary operators), `bool32_eq0`;
* memory: `ld32_eq` (the low half of a `u64`), `ld64_storeLE_same`/`_ne` (reading a written
  slot or another one), `bytesAt_storeLE_disjoint`;
* decoding: the instruction fields of `Silmaril.RiscV.decode` (`extractLsb'`) against the
  simulator's (`%`, `>>>`): `op_iff`, `f3_iff`, `f7_iff`, `f6_iff`, `reg_toNat`; immediates
  `imm_eq`, `up_eq`, `sh_eq`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Mem

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (leNat bytesAt storeLE)

variable {H : Type}

/-! ## Wasm evaluation -/

theorem memq {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    (h : MemAt s mi ma mt B) (ls : List (Option Val)) :
    s.mem? ⟨ls, mi⟩ ⟨0⟩ = some (ma, ⟨mt, B⟩) := by
  simp [Store.mem?, Idx.toNat, h.1, h.2]

theorem load_ite (B : ByteArray) (a n : Nat) : Memory.load B a n =
    if a + n ≤ B.size then some (BitVec.ofNat (8 * n) (leNat (bytesAt B ⟨a, n⟩))) else none := by
  split
  · exact Silmaril.Wasm.Logic.Core.load_eq ‹_›
  · exact Silmaril.Wasm.Logic.Core.load_eq_none (by omega)

theorem load8 (B : ByteArray) (a : Nat) : Memory.load B a 8 =
    if a + 8 ≤ B.size then some (ld64 B a) else none := load_ite B a 8

theorem load4 (B : ByteArray) (a : Nat) : Memory.load B a 4 =
    if a + 4 ≤ B.size then some (ld32 B a) else none := load_ite B a 4

section
variable {t : IntType} {x y : BitVec t.width}
@[simp] theorem ib_add : intBinOp t .add x y = .ok (x + y) := rfl
@[simp] theorem ib_sub : intBinOp t .sub x y = .ok (x - y) := rfl
@[simp] theorem ib_mul : intBinOp t .mul x y = .ok (x * y) := rfl
@[simp] theorem ib_and : intBinOp t .and x y = .ok (x &&& y) := rfl
@[simp] theorem ib_or : intBinOp t .or x y = .ok (x ||| y) := rfl
@[simp] theorem ib_xor : intBinOp t .xor x y = .ok (x ^^^ y) := rfl
@[simp] theorem ib_shl : intBinOp t .shl x y = .ok (x <<< (y.toNat % t.width)) := rfl
@[simp] theorem ib_shru : intBinOp t (.shr .unsigned) x y = .ok (x >>> (y.toNat % t.width)) := rfl
@[simp] theorem ib_shrs : intBinOp t (.shr .signed) x y = .ok (x.sshiftRight (y.toNat % t.width)) :=
  rfl
end

section
variable {x y : BitVec 64}
@[simp] theorem ib_add64 : intBinOp .i64 .add x y = .ok (x + y) := rfl
@[simp] theorem ib_sub64 : intBinOp .i64 .sub x y = .ok (x - y) := rfl
@[simp] theorem ib_mul64 : intBinOp .i64 .mul x y = .ok (x * y) := rfl
@[simp] theorem ib_and64 : intBinOp .i64 .and x y = .ok (x &&& y) := rfl
@[simp] theorem ib_or64 : intBinOp .i64 .or x y = .ok (x ||| y) := rfl
@[simp] theorem ib_xor64 : intBinOp .i64 .xor x y = .ok (x ^^^ y) := rfl
@[simp] theorem ib_shl64 : intBinOp .i64 .shl x y = .ok (x <<< (y.toNat % 64)) := rfl
@[simp] theorem ib_shru64 : intBinOp .i64 (.shr .unsigned) x y = .ok (x >>> (y.toNat % 64)) := rfl
@[simp] theorem ib_shrs64 : intBinOp .i64 (.shr .signed) x y = .ok (x.sshiftRight (y.toNat % 64)) :=
  rfl
end

section
variable {x y : BitVec 32}
@[simp] theorem ib_add32 : intBinOp .i32 .add x y = .ok (x + y) := rfl
@[simp] theorem ib_sub32 : intBinOp .i32 .sub x y = .ok (x - y) := rfl
@[simp] theorem ib_mul32 : intBinOp .i32 .mul x y = .ok (x * y) := rfl
@[simp] theorem ib_and32 : intBinOp .i32 .and x y = .ok (x &&& y) := rfl
@[simp] theorem ib_or32 : intBinOp .i32 .or x y = .ok (x ||| y) := rfl
@[simp] theorem ib_xor32 : intBinOp .i32 .xor x y = .ok (x ^^^ y) := rfl
@[simp] theorem ib_shl32 : intBinOp .i32 .shl x y = .ok (x <<< (y.toNat % 32)) := rfl
@[simp] theorem ib_shru32 : intBinOp .i32 (.shr .unsigned) x y = .ok (x >>> (y.toNat % 32)) := rfl
@[simp] theorem ib_shrs32 : intBinOp .i32 (.shr .signed) x y = .ok (x.sshiftRight (y.toNat % 32)) :=
  rfl
end

@[simp] theorem ib_remu64 (x y : BitVec 64) (hy : y ≠ 0#64) :
    intBinOp .i64 (.rem .unsigned) x y = .ok (x % y) := by
  simp only [intBinOp]; exact ite_eq_right_of_eq_false _ _ (eq_false hy) |>.trans rfl

@[simp] theorem ib_remu32 (x y : BitVec 32) (hy : y ≠ 0#32) :
    intBinOp .i32 (.rem .unsigned) x y = .ok (x % y) := by
  simp only [intBinOp]; exact ite_eq_right_of_eq_false _ _ (eq_false hy) |>.trans rfl

@[simp] theorem bool32_eq0 (b : Bool) : bool32 b = 0#32 ↔ b = false := by cases b <;> decide

@[simp] theorem bool32_eq0' (b : Bool) : bool32 b = (0 : BitVec 32) ↔ b = false := by
  cases b <;> decide

/-- The frame of `step` with its eight locals. -/
def frm (mi : ModuleInst) (pc en : BitVec 64) (w : BitVec 32) (w64 : BitVec 64) (rd : BitVec 32)
    (a b v : BitVec 64) : Frame :=
  ⟨[some (.num ⟨.int .i64, pc⟩), some (.num ⟨.int .i64, en⟩), some (.num ⟨.int .i32, w⟩),
    some (.num ⟨.int .i64, w64⟩), some (.num ⟨.int .i32, rd⟩), some (.num ⟨.int .i64, a⟩),
    some (.num ⟨.int .i64, b⟩), some (.num ⟨.int .i64, v⟩)], mi⟩

/-! ## Memory -/

theorem bytesAt_split (B : ByteArray) (a m n : Nat) :
    bytesAt B ⟨a, m + n⟩ = bytesAt B ⟨a, m⟩ ++ bytesAt B ⟨a + m, n⟩ := by
  simp only [bytesAt, List.take_add, List.drop_drop]

theorem ld32_eq (B : ByteArray) (a : Nat) (h : a + 8 ≤ B.size) :
    ld32 B a = (ld64 B a).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  have hs := bytesAt_split B a 4 4
  have hl : (bytesAt B ⟨a, 4⟩).length = 4 :=
    Silmaril.Wasm.Logic.Core.length_bytesAt (r := ⟨a, 4⟩)
      (by simp [Silmaril.Wasm.Logic.Core.Region.InBounds, Silmaril.Wasm.Logic.Core.Region.stop]; omega)
  simp only [ld32, ld64, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  rw [show (8 : Nat) = 4 + 4 from rfl, hs, Silmaril.Wasm.Logic.Core.leNat_append, hl]
  omega

theorem ld32_zero_toNat (B : ByteArray) (h8 : 8 ≤ B.size) (hpc : (ld64 B 0).toNat < 2 ^ 32) :
    (ld32 B 0).toNat = (ld64 B 0).toNat := by
  rw [ld32_eq B 0 (by omega), BitVec.toNat_setWidth]; omega


/-! ## Stores -/

theorem store_ite (B : ByteArray) (a : Nat) (v : BitVec (8 * 8)) :
    Memory.store B a (count := 8) v =
      if a + 8 ≤ B.size then some (storeLE B a 8 v.toNat) else none := by
  split
  · exact Silmaril.Wasm.Logic.Core.store_eq v ‹_›
  · simp only [Memory.store, Memory.writeBytes, Memory.encodeLE_size]; rw [ite_eq_right (by omega)]

theorem size_storeLE {B : ByteArray} {a : Nat} (v : Nat) (h : a + 8 ≤ B.size) :
    (storeLE B a 8 v).size = B.size := by
  have hw : Memory.writeBytes B a (Memory.encodeLE 8 v) = some (storeLE B a 8 v) := by
    simp only [Memory.writeBytes, storeLE, Memory.encodeLE_size, h, ↓reduceIte]
  exact Memory.writeBytes_size B _ _ a hw

theorem storeLE_ofNat {B : ByteArray} {a : Nat} (v : BitVec 64) :
    storeLE B a 8 v.toNat = storeLE B a 8 (BitVec.ofNat (8 * 8) v.toNat).toNat := by
  simp

theorem ld64_storeLE_same {B : ByteArray} {a : Nat} (v : BitVec 64) (h : a + 8 ≤ B.size) :
    ld64 (storeLE B a 8 v.toNat) a = v := by
  have hs := Silmaril.Wasm.Logic.Core.store_eq (B := B) (n := 8) v h
  have hl := Silmaril.Wasm.Logic.Core.load_store_same hs
  rw [load8, ite_eq_left (by rw [size_storeLE _ h]; exact h)] at hl
  exact Option.some.inj hl

theorem ld64_storeLE_ne {B : ByteArray} {a b : Nat} (v : BitVec 64) (h : a + 8 ≤ B.size)
    (hb : b + 8 ≤ B.size) (hd : a + 8 ≤ b ∨ b + 8 ≤ a) :
    ld64 (storeLE B a 8 v.toNat) b = ld64 B b := by
  have hs := Silmaril.Wasm.Logic.Core.store_eq (B := B) (n := 8) v h
  have hl := Silmaril.Wasm.Logic.Core.load_store_disjoint (b := b) (m := 8) hs
    (by simp [Silmaril.Wasm.Logic.Core.Region.Disjoint, Silmaril.Wasm.Logic.Core.Region.stop]; omega)
  rw [load8, load8, ite_eq_left (by rw [size_storeLE _ h]; exact hb), ite_eq_left hb] at hl
  exact Option.some.inj hl

theorem writeBytes_storeLE {B : ByteArray} {a : Nat} (v : Nat) (h : a + 8 ≤ B.size) :
    Memory.writeBytes B a (Memory.encodeLE 8 v) = some (storeLE B a 8 v) := by
  simp only [Memory.writeBytes, storeLE, Memory.encodeLE_size, h, ↓reduceIte]

/-- Nat-valued forms (what `wpc` produces for `i64.store`). -/
theorem ld64_storeLE_same_nat {B : ByteArray} {a : Nat} (v : Nat) (h : a + 8 ≤ B.size) :
    ld64 (storeLE B a 8 v) a = BitVec.ofNat 64 v := by
  have hb := Silmaril.Wasm.Logic.Core.bytesAt_writeBytes_inside' (r := ⟨a, 8⟩)
    (writeBytes_storeLE v h)
    (by simp [Silmaril.Wasm.Logic.Core.Region.Contains, Silmaril.Wasm.Logic.Core.Region.stop])
  simp only [Nat.sub_self] at hb
  have hl : bytesAt (Memory.encodeLE 8 v) ⟨0, 8⟩ = (Memory.encodeLE 8 v).data.toList := by
    simp only [bytesAt, List.drop_zero]
    exact List.take_of_length_le (by simp)
  rw [ld64, hb, hl, Silmaril.Wasm.Logic.Core.leNat_encodeLE]
  apply BitVec.eq_of_toNat_eq; simp

theorem ld64_storeLE_ne_nat {B : ByteArray} {a b : Nat} (v : Nat) (h : a + 8 ≤ B.size)
    (hd : a + 8 ≤ b ∨ b + 8 ≤ a) : ld64 (storeLE B a 8 v) b = ld64 B b := by
  simp only [ld64, Silmaril.Wasm.Logic.Core.bytesAt_writeBytes_disjoint (r := ⟨b, 8⟩)
    (writeBytes_storeLE v h)
    (by simp [Silmaril.Wasm.Logic.Core.Region.Disjoint, Silmaril.Wasm.Logic.Core.Region.stop]; omega)]

theorem ld32_storeLE_ne_nat {B : ByteArray} {a b : Nat} (v : Nat) (h : a + 8 ≤ B.size)
    (hd : a + 8 ≤ b ∨ b + 4 ≤ a) : ld32 (storeLE B a 8 v) b = ld32 B b := by
  simp only [ld32, Silmaril.Wasm.Logic.Core.bytesAt_writeBytes_disjoint (r := ⟨b, 4⟩)
    (writeBytes_storeLE v h)
    (by simp [Silmaril.Wasm.Logic.Core.Region.Disjoint, Silmaril.Wasm.Logic.Core.Region.stop]; omega)]

theorem size_storeLE' {B : ByteArray} {a : Nat} (v : Nat) (h : a + 8 ≤ B.size) :
    (storeLE B a 8 v).size = B.size := size_storeLE v h

theorem ld32_storeLE_ne {B : ByteArray} {a b : Nat} (v : BitVec 64) (h : a + 8 ≤ B.size)
    (hb : b + 4 ≤ B.size) (hd : a + 8 ≤ b ∨ b + 4 ≤ a) :
    ld32 (storeLE B a 8 v.toNat) b = ld32 B b := by
  have hs := Silmaril.Wasm.Logic.Core.store_eq (B := B) (n := 8) v h
  have hl := Silmaril.Wasm.Logic.Core.load_store_disjoint (b := b) (m := 4) hs
    (by simp [Silmaril.Wasm.Logic.Core.Region.Disjoint, Silmaril.Wasm.Logic.Core.Region.stop]; omega)
  rw [load4, load4, ite_eq_left (by rw [size_storeLE _ h]; exact hb), ite_eq_left hb] at hl
  exact Option.some.inj hl

theorem sameOutside_storeLE {B : ByteArray} {p len a : Nat} (v : BitVec 64) (ha : a + 8 ≤ B.size)
    (hp : p ≤ a) (hl : a + 8 ≤ p + len) : SameOutside B (storeLE B a 8 v.toNat) p len := by
  have hw : Memory.writeBytes B a (Memory.encodeLE 8 v.toNat) = some (storeLE B a 8 v.toNat) :=
    Silmaril.Wasm.Logic.Core.store_eq (n := 8) v ha
  obtain ⟨hb, hL⟩ := Silmaril.Wasm.Logic.Core.toList_writeBytes hw
  have hsz : (Memory.encodeLE 8 v.toNat).size = 8 := Memory.encodeLE_size 8 v.toNat
  have hlen : a + (Memory.encodeLE 8 v.toNat).data.toList.length ≤ B.data.toList.length := by
    simp only [Array.length_toList, ByteArray.size_data]
    exact (show (Memory.encodeLE 8 v.toNat).data.size = 8 from hsz) ▸ ha
  refine ⟨size_storeLE _ ha, fun i hi => ?_⟩
  rw [hL, show (Memory.encodeLE 8 v.toNat).size = (Memory.encodeLE 8 v.toNat).data.toList.length
    from rfl, Silmaril.Wasm.Logic.Core.getElem?_splice hlen]
  have hd : (Memory.encodeLE 8 v.toNat).data.toList.length = 8 := by
    simp only [Array.length_toList, ByteArray.size_data]; exact hsz
  split
  · omega
  · rfl

theorem mem?_setMem {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    (h : MemAt s mi ma mt B) (m : MemInst) (ls : List (Option Val)) :
    (s.setMem ma m).mem? ⟨ls, mi⟩ ⟨0⟩ = some (ma, m) := by
  have hlt : ma < s.mems.length := by
    by_contra hc
    have := h.2
    rw [List.getElem?_eq_none (by omega)] at this
    cases this
  simp [Store.mem?, Store.setMem, Idx.toNat, h.1, hlt]


/-! ## Decoding -/

theorem op_iff (w : BitVec 32) (c : BitVec 7) :
    w.extractLsb' 0 7 = c ↔ w % 128#32 = c.setWidth 32 := by
  have := c.isLt
  simp only [← BitVec.toNat_inj, BitVec.extractLsb'_toNat, BitVec.toNat_umod,
    BitVec.toNat_setWidth]
  simp
  omega

theorem f3_iff (w : BitVec 32) (c : BitVec 3) :
    w.extractLsb' 12 3 = c ↔ (w >>> 12) % 8#32 = c.setWidth 32 := by
  have := c.isLt
  simp only [← BitVec.toNat_inj, BitVec.extractLsb'_toNat, BitVec.toNat_umod,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  simp
  omega

theorem f7_iff (w : BitVec 32) (c : BitVec 7) :
    w.extractLsb' 25 7 = c ↔ w >>> 25 = c.setWidth 32 := by
  have := c.isLt
  have := w.isLt
  simp only [← BitVec.toNat_inj, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]
  simp [Nat.shiftRight_eq_div_pow]
  omega

theorem f6_iff (w : BitVec 32) (c : BitVec 6) :
    w.extractLsb' 26 6 = c ↔ w >>> 26 = c.setWidth 32 := by
  have := c.isLt
  have := w.isLt
  simp only [← BitVec.toNat_inj, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]
  simp [Nat.shiftRight_eq_div_pow]
  omega

theorem reg_toNat (w : BitVec 32) (s : Nat) :
    ((w >>> s) % 32#32).toNat = (w.extractLsb' s 5).toNat := by
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_umod, BitVec.toNat_ushiftRight]

/-- A source register read by the simulator: `x0` is `0`, `x_r` is the `u64` at `8 r`. -/
theorem read_reg (B : ByteArray) (w : BitVec 32) (s : Nat) :
    (absState B).read (w.extractLsb' s 5) =
      if (w >>> s) % 32#32 = 0#32 then 0 else ld64 B (w.toNat >>> s % 32 * 8 % 4294967296) := by
  have hz : (w.extractLsb' s 5 = 0#5) ↔ ((w >>> s) % 32#32 = 0#32) := by
    rw [← BitVec.toNat_inj, ← BitVec.toNat_inj, ← reg_toNat]; simp
  have ha : w.toNat >>> s % 32 * 8 % 4294967296 = 8 * (w.extractLsb' s 5).toNat := by
    rw [← reg_toNat]; simp [BitVec.toNat_umod, BitVec.toNat_ushiftRight]; omega
  simp only [Silmaril.RiscV.State.read, absState, ha]
  by_cases h : w.extractLsb' s 5 = 0#5
  · simp [h, hz.mp h]
  · simp [h, mt hz.mpr h]

/-- The destination of a decoded instruction is its `rd` field. -/
theorem dest_of_decode {w : BitVec 32} {i : Silmaril.RiscV.Instr}
    (h : Silmaril.RiscV.decode w = some i) : i.dest = w.extractLsb' 7 5 := by
  rw [← Silmaril.RiscV.encode_decode h]
  cases i <;>
  · ext j hj
    simp only [Silmaril.RiscV.encode, Silmaril.RiscV.Instr.dest, ← BitVec.getLsbD_eq_getElem,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp [hj, show ¬ 7 + j < 7 by omega, show 7 + j - 7 = j by omega]

theorem sh_eq (w : BitVec 32) :
    ((w.setWidth 64 >>> 20) % 64#64).toNat % 64 = (w.extractLsb' 20 6).toNat := by
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_umod, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

theorem imm_eq (w : BitVec 32) :
    ((w.setWidth 64) <<< 32).sshiftRight 52 = (w.extractLsb' 20 12).signExtend 64 := by
  ext i hi
  simp [BitVec.getElem_sshiftRight, BitVec.getElem_signExtend, BitVec.msb_eq_getLsbD_last]
  by_cases h : i < 12
  · simp [h, show 52 + i < 64 by omega, show ¬ 52 + i < 32 by omega,
      show 52 + i - 32 = 20 + i by omega]
  · simp [h, show ¬ 52 + i < 64 by omega]

theorem up_eq (w : BitVec 32) :
    ((w.setWidth 64) <<< 32).sshiftRight 44 <<< 12 = (w.extractLsb' 12 20 ++ 0#12).signExtend 64 := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_sshiftRight]
  simp [BitVec.msb_eq_getLsbD_last]
  by_cases h : i < 32
  · by_cases h2 : i < 12
    · simp [h, h2]
    · simp [h, h2, show 44 + (i - 12) < 64 by omega, show 44 + (i - 12) - 32 = 12 + (i - 12) by omega,
        show i - 12 < 20 by omega, show ¬ 64 ≤ i - 12 by omega, hi,
        show ¬ (44 + (i - 12) < 32) by omega, show 12 + (i - 12) < 64 by omega]
  · by_cases h3 : 44 + (i - 12) < 64
    · omega
    · simp [h, h3, show ¬ i < 12 by omega, show ¬ 64 ≤ i - 12 by omega, hi,
        ← BitVec.getLsbD_eq_getElem]
      rw [BitVec.getLsbD_append]; simp


theorem bw_slt (x y : BitVec 64) :
    (BitVec.ofBool (x.slt y)).setWidth 64 = if x.toInt < y.toInt then 1#64 else 0#64 := by
  by_cases h : x.toInt < y.toInt <;> simp [BitVec.slt, h]

theorem bw_ult (x y : BitVec 64) :
    (BitVec.ofBool (x.ult y)).setWidth 64 = if x.toNat < y.toNat then 1#64 else 0#64 := by
  by_cases h : x.toNat < y.toNat <;> simp [BitVec.ult, h]


theorem frm_v {s : Store H} {C : Store H → Frame → List Val → Prop} {mi : ModuleInst}
    {pc en w64 a b v v' : BitVec 64} {w rd : BitVec 32} (h : v = v')
    (hc : C s (frm mi pc en w w64 rd a b v') []) : C s (frm mi pc en w w64 rd a b v) [] :=
  h ▸ hc

end Silmaril.Sim.RV64.Mem
