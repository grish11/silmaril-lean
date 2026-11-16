module

public import Silmaril.Proofs.Sim.X86.GM.Wrap
public import Silmaril.Wasm.Logic.Memory.Thms
public import Silmaril.X86.Ext.Semantics

/-!
# GM: the memory abstraction

* `exec1_load64`, `exec1_store64`: the Wasm 64-bit accesses;
* **`MemEnc.load`**: in the window, the x86 load (`Ext.loadN`) and the Wasm load at the
  translated address give the same value;
* **`MemEnc.store`**: in the window, the x86 store (`Ext.storeN`) and the Wasm store at the
  translated address both succeed, the abstraction is preserved, and the x86 memory changes only
  inside the window (`WritesWithin`);
* globals are untouched by memory writes (`gval_setMem`, `Layout.setMem`).
-/

@[expose] public section

namespace Silmaril.Sim.X86.GM

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State)
open Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Core (exec exec1 exec_cons exec_nil exec_append bytesAt leNat
  getElem?_bytesAt load_eq toList_encodeLE leNat_cons)

variable {H : Type} {s : Store H} {f : Frame}

/-! ## Wasm accesses -/

theorem exec1_load64 {ma : Nat} {mi : MemInst} (hm : s.mem? f ⟨0⟩ = some (ma, mi)) {a : BitVec 32}
    {v : BitVec 64} (hl : Memory.load mi.bytes a.toNat 8 = some v) (rs : List Val) :
    exec1 s f (Val.i32 a :: rs) (.intLoad .i64 none ⟨0⟩ marg) = some (s, f, Val.i64 v :: rs) := by
  have e : exec1 s f (Val.i32 a :: rs) (.intLoad .i64 none ⟨0⟩ marg) =
      (Memory.load mi.bytes a.toNat 8).map (fun c => (s, f, Val.i64 (c.setWidth 64) :: rs)) := by
    simp only [exec1, Silmaril.Wasm.Logic.Core.popInt, Option.bind_some, hm, Val.i32]
    rfl
  rw [e, hl]
  simp

theorem exec1_store64 {ma : Nat} {mi : MemInst} (hm : s.mem? f ⟨0⟩ = some (ma, mi))
    {a : BitVec 32} {v : BitVec 64} {B' : ByteArray}
    (hs : Memory.store mi.bytes a.toNat (count := 8) v = some B') (rs : List Val) :
    exec1 s f (Val.i64 v :: Val.i32 a :: rs) (.intStore .i64 none ⟨0⟩ marg) =
      some (s.setMem ma { mi with bytes := B' }, f, rs) := by
  have e : exec1 s f (Val.i64 v :: Val.i32 a :: rs) (.intStore .i64 none ⟨0⟩ marg) =
      (Memory.store mi.bytes a.toNat (count := 8) (v.setWidth 64)).map
        (fun b => (s.setMem ma { mi with bytes := b }, f, rs)) := by
    simp only [exec1, Silmaril.Wasm.Logic.Core.popInt, Option.bind_some, hm, Val.i32, Val.i64]
    rfl
  rw [e]
  simp [hs]

theorem gval_setMem (s : Store H) (f : Frame) (ma : Nat) (mi : MemInst) (l : Loc) :
    gval (s.setMem ma mi) f l = gval s f l := by
  simp only [gval_eq, Store.setMem]

theorem Layout.setMem (h : Layout s f) (ma : Nat) (mi : MemInst) : Layout (s.setMem ma mi) f :=
  ⟨fun l => by obtain ⟨a, h1, h2⟩ := h.addr l; exact ⟨a, h1, by simpa [Store.setMem] using h2⟩,
    h.inj⟩

theorem wbytes_eq {B : ByteArray} (h : wbytes s f = some B) :
    ∃ ma mi, s.mem? f ⟨0⟩ = some (ma, mi) ∧ mi.bytes = B := by
  simp only [wbytes, Option.map_eq_some_iff] at h
  obtain ⟨⟨ma, mi⟩, h1, h2⟩ := h
  exact ⟨ma, mi, h1, h2⟩

theorem wbytes_setMem {ma : Nat} {mi : MemInst} (hm : s.mem? f ⟨0⟩ = some (ma, mi))
    (B' : ByteArray) : wbytes (s.setMem ma { mi with bytes := B' }) f = some B' := by
  simp only [Store.mem?, Option.bind_eq_bind] at hm
  simp only [wbytes, Store.mem?, Store.setMem, Option.bind_eq_bind]
  revert hm
  cases hf : f.module.mems[(⟨0⟩ : MemIdx).toNat]? with
  | none => simp
  | some a =>
    simp only [Option.bind_some]
    cases hs : s.mems[a]? with
    | none => simp
    | some mi' =>
      simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩
      have hlt : a < s.mems.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hs; cases hs
      simp [hlt]

/-! ## Bytes -/

/-- The little-endian value of x86 bytes is that of the same Wasm bytes. -/
theorem leValue_eq (xs : List (BitVec 8)) :
    Silmaril.X86.Ext.leValue xs = leNat (xs.map UInt8.ofBitVec) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Silmaril.X86.Ext.leValue, leNat_cons, ih]

/-- The translated address of an access in the window. -/
theorem off_toNatK {W : Win} {a : Word} {k : Nat} (hk : 0 < k) (hW : W.size ≤ 2 ^ 32)
    (ha : W.HoldsK k a) :
    ((a - W.lo).setWidth 32).toNat = a.toNat - W.lo.toNat ∧
      (a - W.lo).toNat = a.toNat - W.lo.toNat := by
  obtain ⟨h1, h2⟩ := ha
  have hs : (a - W.lo).toNat = a.toNat - W.lo.toNat := by
    rw [BitVec.toNat_sub]; have := a.isLt; have := W.lo.isLt; omega
  refine ⟨?_, hs⟩
  rw [BitVec.toNat_setWidth, hs, Nat.mod_eq_of_lt (by omega)]

theorem off_toNat {W : Win} {a : Word} (hW : W.size ≤ 2 ^ 32) (ha : W.Holds a) :
    ((a - W.lo).setWidth 32).toNat = a.toNat - W.lo.toNat ∧
      (a - W.lo).toNat = a.toNat - W.lo.toNat := off_toNatK (k := 8) (by omega) hW ha

/-- The x86 byte at a window address. -/
noncomputable def xbyte (mem : Silmaril.Process.Memory) (a : Nat) : BitVec 8 :=
  (mem.bytes.get? a).getD 0

theorem MemEnc.byte {mem : Silmaril.Process.Memory} {W : Win} {B : ByteArray}
    (h : MemEnc s f mem W) (hB : wbytes s f = some B) {k : Nat} (hk : k < W.size) :
    mem.permits .read (W.lo.toNat + k) = true ∧
      (W.rw = true → mem.permits .write (W.lo.toNat + k) = true) ∧
      mem.bytes.get? (W.lo.toNat + k) = some (xbyte mem (W.lo.toNat + k)) ∧
      B.data.toList[k]? = some (UInt8.ofBitVec (xbyte mem (W.lo.toNat + k))) := by
  obtain ⟨B₀, hB₀, -, -, -, hb⟩ := h
  rw [hB] at hB₀; cases hB₀
  obtain ⟨hr, hw, x, hx, hx'⟩ := hb k hk
  have hxb : xbyte mem (W.lo.toNat + k) = x := by
    simp only [xbyte]; rw [hx]; rfl
  rw [hxb]
  exact ⟨hr, hw, hx, hx'⟩

/-- **Loads of `k` bytes agree in the window**: the x86 and the Wasm loads read the same
little-endian number. -/
theorem MemEnc.loadK {mem : Silmaril.Process.Memory} {W : Win} (h : MemEnc s f mem W) {a : Word}
    {k : Nat} (ha : W.HoldsK k a) : ∃ B L, wbytes s f = some B ∧
      Silmaril.X86.Ext.loadN mem a k = some (BitVec.ofNat 64 L) ∧
      Memory.load B (a.toNat - W.lo.toNat) k = some (BitVec.ofNat (8 * k) L) := by
  obtain ⟨B, hB, hsz, -, hlim, -⟩ := id h
  obtain ⟨h1, h2⟩ := ha
  let xs : List (BitVec 8) := (List.range k).map fun i => xbyte mem (a.toNat + i)
  have hxs : xs.length = k := by simp [xs]
  have hbyte : ∀ i < k, mem.permits .read (a.toNat + i) = true ∧
      mem.bytes.get? (a.toNat + i) = some (xbyte mem (a.toNat + i)) ∧
      B.data.toList[a.toNat - W.lo.toNat + i]? = some (UInt8.ofBitVec (xbyte mem (a.toNat + i))) := by
    intro i hi
    obtain ⟨hr, -, hg, hw⟩ := MemEnc.byte h hB (k := a.toNat - W.lo.toNat + i) (by omega)
    have e : W.lo.toNat + (a.toNat - W.lo.toNat + i) = a.toNat + i := by omega
    exact ⟨e ▸ hr, e ▸ hg, e ▸ hw⟩
  have hread : mem.readBytes a.toNat k = some xs := by
    have hperm : mem.checkSpan .read a.toNat xs.length = true := by
      rw [Silmaril.Process.Memory.checkSpan_iff, hxs]
      simp only [Silmaril.Process.addressLimit]
      exact ⟨by omega, by omega, fun i hi => (hbyte i hi).1⟩
    have hinst : ∀ i (hi : i < xs.length), mem.bytes.get? (a.toNat + i) = some xs[i] := by
      intro i hi
      have hik : i < k := hxs ▸ hi
      simp only [xs, List.getElem_map, List.getElem_range]
      exact (hbyte i hik).2.1
    have hrw : mem.readWith .read a.toNat xs.length = some xs :=
      Silmaril.Process.Memory.readWith_eq mem .read a.toNat xs hperm hinst
    rw [← hxs]
    exact hrw
  have hwb : bytesAt B ⟨a.toNat - W.lo.toNat, k⟩ = xs.map UInt8.ofBitVec := by
    apply List.ext_getElem?
    intro i
    rw [getElem?_bytesAt]
    by_cases hi : i < k
    · simp only [hi, ite_true, (hbyte i hi).2.2, List.getElem?_map, xs, List.getElem?_range,
        Option.map_some]
    · simp only [hi, ite_false, List.getElem?_map]
      rw [List.getElem?_eq_none (by simp [xs]; omega)]; rfl
  refine ⟨B, leNat (xs.map UInt8.ofBitVec), hB, ?_, (load_eq (by omega)).trans (by rw [hwb])⟩
  simp only [Silmaril.X86.Ext.loadN, hread, Option.map_some, leValue_eq]

/-- **Loads agree in the window.** -/
theorem MemEnc.load {mem : Silmaril.Process.Memory} {W : Win} (h : MemEnc s f mem W) {a : Word}
    (ha : W.Holds a) : ∃ B v, wbytes s f = some B ∧ Silmaril.X86.Ext.loadN mem a 8 = some v ∧
      Memory.load B (a.toNat - W.lo.toNat) 8 = some v := by
  obtain ⟨B, L, hB, h1, h2⟩ := h.loadK (k := 8) ha
  exact ⟨B, _, hB, h1, h2⟩

theorem wordByte_toNat (v : Word) (j : Nat) :
    UInt8.ofBitVec (Silmaril.Machine.LittleEndian.wordByte v j) = UInt8.ofNat (v.toNat / 2 ^ (8 * j)) := by
  apply UInt8.toNat_inj.mp
  simp [Silmaril.Machine.LittleEndian.wordByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

/-- **Stores agree in the window**, and the x86 memory changes only inside it. -/
theorem MemEnc.store {mem : Silmaril.Process.Memory} {W : Win} (h : MemEnc s f mem W)
    (hrw : W.rw = true) {a : Word} (ha : W.Holds a) (v : Word) : ∃ ma mi B' mem', s.mem? f ⟨0⟩ = some (ma, mi) ∧
      Silmaril.X86.Ext.storeN mem a 8 v = some mem' ∧
      Memory.store mi.bytes (a.toNat - W.lo.toNat) (count := 8) v = some B' ∧
      MemEnc (s.setMem ma { mi with bytes := B' }) f mem' W ∧
      mem.WritesWithin mem' W.Mem := by
  obtain ⟨B, hB, hsz, h32, hlim, hb⟩ := h
  obtain ⟨ma, mi, hm, rfl⟩ := wbytes_eq hB
  obtain ⟨h1, h2⟩ := ha
  set off := a.toNat - W.lo.toNat
  have hperm : mem.Permitted .write a.toNat (Silmaril.X86.Ext.leBytes v 8).length := by
    show mem.checkSpan .write a.toNat _ = true
    rw [Silmaril.Process.Memory.checkSpan_iff, Silmaril.X86.Ext.length_leBytes]
    simp only [Silmaril.Process.addressLimit]
    refine ⟨by omega, by omega, fun i hi => ?_⟩
    have := (hb (off + i) (by omega)).2.1 hrw
    rwa [show W.lo.toNat + (off + i) = a.toNat + i by omega] at this
  obtain ⟨mem', hmem'⟩ : ∃ mem', mem.writeBytes a.toNat (Silmaril.X86.Ext.leBytes v 8) = some mem' := by
    have hc : mem.checkSpan .write a.toNat (Silmaril.X86.Ext.leBytes v 8).length = true := hperm
    simp only [Silmaril.Process.Memory.writeBytes, hc, ite_true]
    exact ⟨_, rfl⟩
  have hws := Silmaril.Process.Memory.writeBytes_writesOnly hmem'
  rw [Silmaril.X86.Ext.length_leBytes] at hws
  have hstore : Memory.store mi.bytes off (count := 8) v =
      some (Silmaril.Wasm.Logic.Core.storeLE mi.bytes off 8 v.toNat) :=
    Silmaril.Wasm.Logic.Core.store_eq (B := mi.bytes) (a := off) (n := 8) v (by omega)
  refine ⟨ma, mi, _, mem', hm, hmem', hstore, ⟨_, wbytes_setMem hm _, ?_, h32, hlim, ?_⟩, ?_⟩
  · rw [Silmaril.Wasm.Logic.Core.size_store hstore]; exact hsz
  · intro k hk
    obtain ⟨hr, hw, x, hx, hx'⟩ := hb k hk
    have hregions : mem'.regions = mem.regions := hws.1
    have hperm' : ∀ acc, mem'.permits acc (W.lo.toNat + k) = mem.permits acc (W.lo.toNat + k) := by
      intro acc; simp [Silmaril.Process.Memory.permits, hregions]
    refine ⟨by rw [hperm']; exact hr, fun h => by rw [hperm']; exact hw h, ?_⟩
    have hL := (Silmaril.Wasm.Logic.Core.toList_writeBytes (B := mi.bytes) (p := off)
      (D := Memory.encodeLE 8 v.toNat) hstore).2
    have hD : (Memory.encodeLE 8 v.toNat).data.toList.length = 8 := by
      simp [toList_encodeLE]
    have hp : off + (Memory.encodeLE 8 v.toNat).data.toList.length ≤ mi.bytes.data.toList.length := by
      rw [hD]; simp only [Array.length_toList, ByteArray.size_data]; omega
    by_cases hin : off ≤ k ∧ k < off + 8
    · have hk' : W.lo.toNat + k = a.toNat + (k - off) := by omega
      have hget := Silmaril.Process.Memory.writeBytes_get hmem' (k - off)
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
      refine ⟨_, by rw [hk']; exact hget, ?_⟩
      rw [hL, show (Memory.encodeLE 8 v.toNat).size = (Memory.encodeLE 8 v.toNat).data.toList.length
        from rfl, Silmaril.Wasm.Logic.Core.getElem?_splice hp, hD, ite_eq_left_of_eq_true _ _ (eq_true hin)]
      simp only [toList_encodeLE, Silmaril.X86.Ext.leBytes, List.getElem_ofFn, List.getElem?_map,
        List.getElem?_range (show k - off < 8 by omega), Option.map_some, wordByte_toNat]
    · have hout := hws.2 (W.lo.toNat + k) (by omega)
      refine ⟨x, by rw [hout]; exact hx, ?_⟩
      rw [hL, show (Memory.encodeLE 8 v.toNat).size = (Memory.encodeLE 8 v.toNat).data.toList.length
        from rfl, Silmaril.Wasm.Logic.Core.getElem?_splice hp, hD, ite_eq_right_of_eq_false _ _ (eq_false hin)]
      exact hx'
  · refine ⟨hws.1, fun l hl => hws.2 l ?_⟩
    simp only [Win.Mem, not_and, not_lt] at hl
    omega

end Silmaril.Sim.X86.GM
