module

public import Silmaril.Proofs.Wasm.Jco.Real.Exec
public import Silmaril.Wasm.Jco.Real.StepX.Defs

/-!
# `memory.copy` against the reference engine

Core 3.0 runs `memory.copy d s n` byte by byte: front to back when `d ≤ s` (`copy-le`), back to
front otherwise (`copy-gt`), each byte an `i32.load8_u` and an `i32.store8`. On a list memory
`L` of at most `2^32` bytes this computes `mmove L d s n`, the `memmove` that the abstract
adaptor performs (`Mem.read` then `Mem.write`, `write_read_mmove`):

* `mmove_fwd`, `mmove_bwd`: one byte copied first (forwards) or last (backwards), then the rest;
* `core_byte`: the `load8_u`/`store8` pair on the memory of `realInst`;
* **`core_copy`**: the whole copy, by induction on the length.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Real
open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H) (ma : Nat)

/-! ## `memmove` on list memories -/

/-- `memmove`: byte `x` of the result is byte `s + (x - d)` of `L` when `d ≤ x < d + n`. -/
def mmove (L : List UInt8) (d s n : Nat) : List UInt8 :=
  (List.range L.length).map fun x => if d ≤ x ∧ x < d + n then L.getD (s + (x - d)) 0 else L.getD x 0

theorem length_mmove (L : List UInt8) (d s n : Nat) : (mmove L d s n).length = L.length := by
  simp [mmove]

theorem getD_mmove (L : List UInt8) (d s n x : Nat) (hx : x < L.length) :
    (mmove L d s n).getD x 0 = if d ≤ x ∧ x < d + n then L.getD (s + (x - d)) 0 else L.getD x 0 := by
  simp [mmove, List.getD_eq_getElem?_getD, hx]

theorem ext_getD {A B : List UInt8} (hl : A.length = B.length)
    (h : ∀ x, x < A.length → A.getD x 0 = B.getD x 0) : A = B := by
  apply List.ext_getElem hl
  intro x h1 h2
  have := h x h1
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

theorem getD_set (L : List UInt8) (a x : Nat) (v : UInt8) (ha : a < L.length) :
    (L.set a v).getD x 0 = if x = a then v else L.getD x 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hx : x = a
  · subst hx; simp [ha]
  · simp [Ne.symm hx, hx]

theorem mmove_zero (L : List UInt8) (d s : Nat) : mmove L d s 0 = L := by
  apply ext_getD (length_mmove ..)
  intro x hx
  rw [getD_mmove _ _ _ _ _ (by simpa [length_mmove] using hx)]
  simp

/-- **Forwards**: copy byte `s` to `d`, then the remaining `k` bytes. -/
theorem mmove_fwd (L : List UInt8) {d s k : Nat} (hle : d ≤ s) (hs : s + (k + 1) ≤ L.length) :
    mmove (L.set d (L.getD s 0)) (d + 1) (s + 1) k = mmove L d s (k + 1) := by
  have hd : d < L.length := by omega
  apply ext_getD (by simp [length_mmove])
  intro x hx
  simp only [length_mmove, List.length_set] at hx
  rw [getD_mmove _ _ _ _ _ (by simpa using hx), getD_mmove _ _ _ _ _ hx]
  by_cases h1 : d + 1 ≤ x ∧ x < d + 1 + k
  · have h2 : d ≤ x ∧ x < d + (k + 1) := by omega
    have h4 : s + 1 + (x - (d + 1)) = s + (x - d) := by omega
    rw [ite_eq_left h1, ite_eq_left h2, h4, getD_set _ _ _ _ hd, ite_eq_right (by omega)]
  · rw [ite_eq_right h1, getD_set _ _ _ _ hd]
    by_cases hx' : x = d
    · subst hx'
      rw [ite_eq_left rfl, ite_eq_left (by omega)]
      simp
    · rw [ite_eq_right hx', ite_eq_right (by omega)]

/-- **Backwards**: copy byte `s + k` to `d + k`, then the first `k` bytes. -/
theorem mmove_bwd (L : List UInt8) {d s k : Nat} (hlt : s < d) (hd : d + (k + 1) ≤ L.length) :
    mmove (L.set (d + k) (L.getD (s + k) 0)) d s k = mmove L d s (k + 1) := by
  have hdk : d + k < L.length := by omega
  apply ext_getD (by simp [length_mmove])
  intro x hx
  simp only [length_mmove, List.length_set] at hx
  rw [getD_mmove _ _ _ _ _ (by simpa using hx), getD_mmove _ _ _ _ _ hx]
  by_cases h1 : d ≤ x ∧ x < d + k
  · rw [ite_eq_left h1, ite_eq_left (by omega), getD_set _ _ _ _ hdk, ite_eq_right (by omega)]
  · rw [ite_eq_right h1, getD_set _ _ _ _ hdk]
    by_cases hx' : x = d + k
    · subst hx'
      rw [ite_eq_left rfl, ite_eq_left (by omega)]
      congr 1
      omega
    · rw [ite_eq_right hx', ite_eq_right (by omega)]

/-- The abstract copy (`Mem.read` then `Mem.write`) is `mmove`. -/
theorem write_read_mmove {L bs m' : List UInt8} {d s n : Nat} (hr : Mem.read L s n = some bs)
    (hw : Mem.write L d bs = some m') :
    m' = mmove L d s n ∧ d + n ≤ L.length ∧ s + n ≤ L.length := by
  unfold Mem.read at hr
  split at hr
  · rename_i hsn
    cases hr
    unfold Mem.write at hw
    have hlen : ((L.drop s).take n).length = n := by simp; omega
    rw [hlen] at hw
    split at hw
    · rename_i hdn
      cases hw
      refine ⟨?_, hdn, hsn⟩
      have hA : (L.take d).length = d := by simp; omega
      apply ext_getD (by simp [length_mmove]; omega)
      intro x hx
      have hx' : x < L.length := by simp at hx; omega
      rw [getD_mmove _ _ _ _ _ hx', List.getD_eq_getElem?_getD, List.append_assoc]
      by_cases hx1 : x < d
      · rw [List.getElem?_append_left (by rw [hA]; exact hx1), List.getElem?_take,
          ite_eq_left hx1, ite_eq_right (by omega), List.getD_eq_getElem?_getD]
      · rw [List.getElem?_append_right (by rw [hA]; omega), hA]
        by_cases hx2 : x < d + n
        · rw [List.getElem?_append_left (by rw [hlen]; omega), List.getElem?_take,
            ite_eq_left (by omega), List.getElem?_drop, ite_eq_left (by omega),
            List.getD_eq_getElem?_getD]
        · rw [List.getElem?_append_right (by rw [hlen]; omega), hlen, List.getElem?_drop,
            ite_eq_right (by omega), List.getD_eq_getElem?_getD]
          congr 2
          omega
    · cases hw
  · cases hr

/-! ## The store of `realInst` -/

theorem memBytes_some {s : Store H} {m : MemInst} (hm : s.mems[ma]? = some m) :
    memBytes ma s = m.bytes.data.toList := by
  simp [memBytes, hm]

theorem memBytes_putBytes {s : Store H} {m : MemInst} (hm : s.mems[ma]? = some m)
    (L : List UInt8) : memBytes ma (putBytes ma s L) = L := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hm
  simp [memBytes, putBytes, Store.setMem, hlt]

theorem mems_putBytes {s : Store H} {m : MemInst} (hm : s.mems[ma]? = some m)
    (L : List UInt8) : (putBytes ma s L).mems[ma]? = some { m with bytes := ⟨L.toArray⟩ } := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hm
  simp [putBytes, Store.setMem, hlt, heq]

theorem putBytes_putBytes {s : Store H} {m : MemInst} (hm : s.mems[ma]? = some m)
    (L₁ L₂ : List UInt8) : putBytes ma (putBytes ma s L₁) L₂ = putBytes ma s L₂ := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hm
  have h1 := mems_putBytes ma hm L₁
  unfold putBytes at h1 ⊢
  rw [h1, hm]
  simp only [Store.setMem, List.set_set]

theorem putBytes_self {s : Store H} : putBytes ma s (memBytes ma s) = s := by
  cases hm : s.mems[ma]? with
  | none => simp [putBytes, hm]
  | some m =>
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hm
    simp only [putBytes, memBytes, hm, Store.setMem]
    have hb : ({ m with bytes := ⟨m.bytes.data.toList.toArray⟩ } : MemInst) = m := by simp
    rw [hb, ← heq, List.set_getElem_self]
theorem MemOk.length {s : Store H} (h : MemOk ma s) : (memBytes ma s).length ≤ 2 ^ 32 := by
  obtain ⟨m, hm, hs⟩ := h
  rw [memBytes_some ma hm, size_toList]
  exact hs

theorem MemOk.putBytes {s : Store H} (h : MemOk ma s) {L : List UInt8}
    (hL : L.length = (memBytes ma s).length) : MemOk ma (putBytes ma s L) := by
  obtain ⟨m, hm, hs⟩ := h
  refine ⟨_, mems_putBytes ma hm L, ?_⟩
  rw [memBytes_some ma hm, size_toList] at hL
  show L.toArray.size ≤ _
  simpa [hL] using hs

/-! ## One byte -/

/-- `i32.const x`. -/
abbrev i32a (x : BitVec 32) : Admin := .plain (.intConst .i32 x)

theorem write_one (L : List UInt8) {a : Nat} (ha : a < L.length) (b : UInt8) :
    Mem.write L a [b] = some (L.set a b) := by
  unfold Mem.write
  rw [ite_eq_left (by simp; omega), List.set_eq_take_append_cons_drop, ite_eq_left ha]
  simp

theorem read_one (L : List UInt8) {a : Nat} (ha : a < L.length) :
    Mem.read L a 1 = some [L.getD a 0] := by
  unfold Mem.read
  rw [ite_eq_left (by omega)]
  simp [List.getD_eq_getElem?_getD, ha, List.take_one, List.head?_drop]

theorem leBytes_one (b : UInt8) : leBytes 1 b.toNat = [b] := by
  simp only [leBytes, List.cons.injEq, and_true]
  apply UInt8.toNat_inj.mp
  simp [Nat.toUInt8, Nat.mod_eq_of_lt b.toNat_lt]

/-- **One byte copied by `i32.load8_u` and `i32.store8`.** -/
theorem core_byte {s : Store H} {cf : Silmaril.Wasm.Execution.Core.Frame}
    (hmem : cf.module.mems[0]? = some ma) {L : List UInt8} (hL : memBytes ma s = L)
    {d src : BitVec 32} (hd : d.toNat < L.length) (hs : src.toNat < L.length) :
    Steps P host ⟨s, cf, [i32a d, i32a src, load8u ⟨0⟩, store8 ⟨0⟩]⟩
      ⟨putBytes ma s (L.set d.toNat (L.getD src.toNat 0)), cf, []⟩ := by
  have hr : (memBytes ma s).read src.toNat 1 = some [L.getD src.toNat 0] := by
    rw [hL]; exact read_one L hs
  obtain ⟨m, hm, hload⟩ := memBytes_load (n := 1) (by decide) hr
  have hsm : s.mem? cf ⟨0⟩ = some (ma, m) := by
    simp [Store.mem?, Silmaril.Wasm.Idx.toNat, hmem, hm]
  have hw : (memBytes ma s).write d.toNat (leBytes 1 (L.getD src.toNat 0).toNat) =
      some (L.set d.toNat (L.getD src.toNat 0)) := by
    rw [leBytes_one, hL]; exact write_one L hd _
  obtain ⟨m₂, B, hm₂, hstore, hput⟩ := memBytes_store (n := 1) (by decide) hw
  rw [hm] at hm₂
  cases hm₂
  generalize L.getD src.toNat 0 = b at hload hstore hput
  have hleNat : leNat [b] = b.toNat := by simp [leNat]
  rw [hleNat] at hload
  have hset : ((BitVec.ofNat 8 b.toNat).setWidth 32).setWidth 8 = BitVec.ofNat 8 b.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp
  have hl' : Silmaril.Wasm.Execution.Memory.load m.bytes (effAddr src.toNat memarg0) 1 =
      some (BitVec.ofNat 8 b.toNat) := hload
  have hs' : Silmaril.Wasm.Execution.Memory.store m.bytes (effAddr d.toNat memarg0) (count := 1)
      (((BitVec.ofNat 8 b.toNat).setWidth 32).setWidth 8) = some B := by
    rw [hset]; exact hstore
  have h1 : Step P host ⟨s, cf, [i32a src, load8u ⟨0⟩]⟩
      ⟨s, cf, [.plain (.intConst .i32 ((BitVec.ofNat 8 b.toNat).setWidth 32))]⟩ :=
    Step.memory (MemoryStep.loadPackVal (t := .i32) (sx := .unsigned) (sz := .i8) (a := .i32)
      (i := src) (arg := memarg0) hsm hl')
  have h2 : Step P host ⟨s, cf, [i32a d, .plain (.intConst .i32 ((BitVec.ofNat 8 b.toNat).setWidth 32)),
      store8 ⟨0⟩]⟩ ⟨s.setMem ma { m with bytes := B }, cf, []⟩ :=
    Step.memory (MemoryStep.storePackVal (t := .i32) (sz := .i8) (a := .i32) (i := d)
      (arg := memarg0) hsm hs')
  have h1' : Steps P host ⟨s, cf, [i32a d, i32a src, load8u ⟨0⟩, store8 ⟨0⟩]⟩
      ⟨s, cf, [i32a d, .plain (.intConst .i32 ((BitVec.ofNat 8 b.toNat).setWidth 32)),
        store8 ⟨0⟩]⟩ :=
    Steps.ctxtInstrs (vs := [Val.i32 d]) (rest := [store8 ⟨0⟩]) h1.steps
  rw [hput]
  exact h1'.trans h2.steps

/-! ## The whole copy -/

theorem toNat_succ {i : BitVec 32} (h : i.toNat + 1 < 2 ^ 32) : (i + 1).toNat = i.toNat + 1 := by
  bv_omega

theorem toNat_succ_le (i : BitVec 32) : (i + 1).toNat ≤ i.toNat + 1 := by
  bv_omega

theorem ofNat_succ_sub {k : Nat} (hk : k + 1 < 2 ^ 32) :
    BitVec.ofNat 32 (k + 1) - 1 = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  have : k < 2 ^ 32 := by omega
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  bv_omega

theorem toNat_last {i : BitVec 32} {k : Nat} (h : i.toNat + k + 1 ≤ 2 ^ 32) (hk : k + 1 < 2 ^ 32) :
    (i + BitVec.ofNat 32 (BitVec.ofNat 32 (k + 1)).toNat - 1).toNat = i.toNat + k := by
  have e : (BitVec.ofNat 32 (k + 1)).toNat = k + 1 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hk
  rw [e]
  bv_omega

/-- **`memory.copy`**: from a store whose memory `ma` is the list `L` (at most `2^32` bytes),
Core's byte-by-byte copy of `k` bytes from `i₂` to `i₁` ends in the store with memory
`mmove L i₁ i₂ k`. -/
theorem core_copy {cf : Silmaril.Wasm.Execution.Core.Frame} (hmem : cf.module.mems[0]? = some ma) :
    ∀ (k : Nat) (i₁ i₂ : BitVec 32) (s : Store H), MemOk ma s →
      i₁.toNat + k ≤ (memBytes ma s).length → i₂.toNat + k ≤ (memBytes ma s).length →
      k < 2 ^ 32 →
      Steps P host ⟨s, cf, [i32a i₁, i32a i₂, i32a (BitVec.ofNat 32 k),
          .plain (.memoryCopy ⟨0⟩ ⟨0⟩)]⟩
        ⟨putBytes ma s (mmove (memBytes ma s) i₁.toNat i₂.toNat k), cf, []⟩
  | 0, i₁, i₂, s, hok, h₁, h₂, _ => by
    obtain ⟨m, hm, -⟩ := hok
    have hsm : s.mem? cf ⟨0⟩ = some (ma, m) := by
      simp [Store.mem?, Silmaril.Wasm.Idx.toNat, hmem, hm]
    have hsz : (memBytes ma s).length = m.bytes.size := by
      rw [memBytes_some ma hm, size_toList]
    have hb₁ : i₁.toNat ≤ m.bytes.size := by omega
    have hb₂ : i₂.toNat ≤ m.bytes.size := by omega
    rw [mmove_zero, putBytes_self]
    exact (Step.memory (MemoryStep.copyZero (a₁ := .i32) (a₂ := .i32) (a' := .i32) (i₁ := i₁)
      (i₂ := i₂) hsm hsm ⟨hb₁, hb₂⟩)).steps
  | k + 1, i₁, i₂, s, hok, h₁, h₂, hk => by
    have hL32 := MemOk.length ma hok
    obtain ⟨m, hm, -⟩ := hok
    have hsm : s.mem? cf ⟨0⟩ = some (ma, m) := by
      simp [Store.mem?, Silmaril.Wasm.Idx.toNat, hmem, hm]
    have hsz : (memBytes ma s).length = m.bytes.size := by
      rw [memBytes_some ma hm, size_toList]
    generalize hL : memBytes ma s = L at h₁ h₂ hsz hL32 ⊢
    have hn : (BitVec.ofNat 32 (k + 1)).toNat = k + 1 := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hk
    have hn0 : BitVec.ofNat 32 (k + 1) ≠ 0 := by
      intro h0; have := congrArg BitVec.toNat h0; rw [hn] at this; simp at this
    have hbound : i₁.toNat + (BitVec.ofNat 32 (k + 1)).toNat ≤ m.bytes.size ∧
        i₂.toNat + (BitVec.ofNat 32 (k + 1)).toNat ≤ m.bytes.size := by
      rw [hn]; omega
    have hk' : k < 2 ^ 32 := by omega
    by_cases hle : i₁.toNat ≤ i₂.toNat
    · -- forwards
      have hstep : Step P host ⟨s, cf, [i32a i₁, i32a i₂, i32a (BitVec.ofNat 32 (k + 1)),
          .plain (.memoryCopy ⟨0⟩ ⟨0⟩)]⟩ ⟨s, cf, [i32a i₁, i32a i₂, load8u ⟨0⟩, store8 ⟨0⟩,
          i32a (i₁ + 1), i32a (i₂ + 1), i32a (BitVec.ofNat 32 (k + 1) - 1),
          .plain (.memoryCopy ⟨0⟩ ⟨0⟩)]⟩ := Step.memory (MemoryStep.copyLe (a₁ := .i32)
        (a₂ := .i32) (a' := .i32) (i₁ := i₁) (i₂ := i₂) (n := BitVec.ofNat 32 (k + 1)) hsm hsm
        hbound hn0 hle)
      have hbyte := core_byte P host ma hmem hL (d := i₁) (src := i₂) (by omega) (by omega)
      set L₁ := L.set i₁.toNat (L.getD i₂.toNat 0) with hL₁
      have hok₁ : MemOk ma (putBytes ma s L₁) := MemOk.putBytes ma
        (show MemOk ma s from ⟨m, hm, by omega⟩) (by simp [hL₁, hL])
      have hmb : memBytes ma (putBytes ma s L₁) = L₁ := memBytes_putBytes ma hm L₁
      have hlen₁ : L₁.length = L.length := by simp [hL₁]
      have ha₁ : (i₁ + 1).toNat + k ≤ L₁.length := by
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · have := toNat_succ_le i₁; omega
        · rw [toNat_succ (by omega)]; omega
      have ha₂ : (i₂ + 1).toNat + k ≤ L₁.length := by
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · have := toNat_succ_le i₂; omega
        · rw [toNat_succ (by omega)]; omega
      have ih := core_copy hmem k (i₁ + 1) (i₂ + 1) (putBytes ma s L₁) hok₁ (by rw [hmb]; exact ha₁)
        (by rw [hmb]; exact ha₂) hk'
      rw [hmb, putBytes_putBytes ma hm] at ih
      have hres : mmove L₁ (i₁ + 1).toNat (i₂ + 1).toNat k = mmove L i₁.toNat i₂.toNat (k + 1) := by
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · rw [mmove_zero, ← mmove_fwd L hle (by omega), mmove_zero]
        · rw [toNat_succ (by omega), toNat_succ (by omega)]
          exact mmove_fwd L hle (by omega)
      rw [hres] at ih
      have hb' := Silmaril.Wasm.Execution.Core.Sim.Steps.append_right hbyte
        [i32a (i₁ + 1), i32a (i₂ + 1), i32a (BitVec.ofNat 32 (k + 1) - 1),
          .plain (.memoryCopy ⟨0⟩ ⟨0⟩)]
      rw [ofNat_succ_sub hk] at hb' hstep
      refine hstep.steps.trans ?_
      exact hb'.trans ih
    · -- backwards
      have hgt : i₂.toNat < i₁.toNat := by omega
      have hstep : Step P host ⟨s, cf, [i32a i₁, i32a i₂, i32a (BitVec.ofNat 32 (k + 1)),
          .plain (.memoryCopy ⟨0⟩ ⟨0⟩)]⟩ ⟨s, cf,
          [i32a (i₁ + BitVec.ofNat 32 (BitVec.ofNat 32 (k + 1)).toNat - 1),
          i32a (i₂ + BitVec.ofNat 32 (BitVec.ofNat 32 (k + 1)).toNat - 1), load8u ⟨0⟩, store8 ⟨0⟩,
          i32a i₁, i32a i₂, i32a (BitVec.ofNat 32 (k + 1) - 1),
          .plain (.memoryCopy ⟨0⟩ ⟨0⟩)]⟩ := Step.memory (MemoryStep.copyGt (a₁ := .i32)
        (a₂ := .i32) (a' := .i32) (i₁ := i₁) (i₂ := i₂) (n := BitVec.ofNat 32 (k + 1)) hsm hsm
        hbound hn0 hgt)
      have e₁ := toNat_last (i := i₁) (k := k) (by omega) hk
      have e₂ := toNat_last (i := i₂) (k := k) (by omega) hk
      have hbyte := core_byte P host ma hmem hL
        (d := i₁ + BitVec.ofNat 32 (BitVec.ofNat 32 (k + 1)).toNat - 1)
        (src := i₂ + BitVec.ofNat 32 (BitVec.ofNat 32 (k + 1)).toNat - 1)
        (by rw [e₁]; omega) (by rw [e₂]; omega)
      rw [e₁, e₂] at hbyte
      set L₁ := L.set (i₁.toNat + k) (L.getD (i₂.toNat + k) 0) with hL₁
      have hok₁ : MemOk ma (putBytes ma s L₁) := MemOk.putBytes ma
        (show MemOk ma s from ⟨m, hm, by omega⟩) (by simp [hL₁, hL])
      have hmb : memBytes ma (putBytes ma s L₁) = L₁ := memBytes_putBytes ma hm L₁
      have ih := core_copy hmem k i₁ i₂ (putBytes ma s L₁) hok₁ (by rw [hmb]; simp [hL₁]; omega)
        (by rw [hmb]; simp [hL₁]; omega) hk'
      rw [hmb, putBytes_putBytes ma hm, mmove_bwd L hgt (by omega)] at ih
      have hb' := Silmaril.Wasm.Execution.Core.Sim.Steps.append_right hbyte
        [i32a i₁, i32a i₂, i32a (BitVec.ofNat 32 (k + 1) - 1), .plain (.memoryCopy ⟨0⟩ ⟨0⟩)]
      rw [ofNat_succ_sub hk] at hb' hstep
      refine hstep.steps.trans ?_
      exact hb'.trans ih

end Silmaril.Proofs.Wasm.Jco.Real
