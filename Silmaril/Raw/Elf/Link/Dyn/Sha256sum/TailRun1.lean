module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailOpts

/-! # GNU `sha256sum`, stdin tier: `main` from `0x29fd` to `0x2ae3` (option checks)

`tail_opts` chains the blocks of `TailOpts`: with `binary` unset, `--check` off, the delimiter
`'\n'` and the five `.bss` flags clear, `main` stores `0x42`/`0x40` into `.bss` (`optMem`) and
reaches `0x2ae3` with `edx = 1`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert

theorem loadN_rb {m : Memory} {A : Word} {a n : Nat} {l : List Byte} (he : A.toNat = a)
    (h : m.readBytes a n = some l) : loadN m A n = some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue l)) := by
  simp [loadN, he, h]

theorem optMem_rb {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) (m : Memory) {a n : Nat}
    (ha : a + n ≤ b.toNat + 0xa168 ∨ (b.toNat + 0xa170 ≤ a ∧ a + n ≤ b.toNat + 0xa178) ∨
      b.toNat + 0xa180 ≤ a) :
    (optMem m b).readBytes a n = m.readBytes a n := by
  have e1 : (b + 0xa168#64).toNat = b.toNat + 0xa168 := addr_toNat (v := 0xa168) (by omega)
  have e2 : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (v := 0xa178) (by omega)
  unfold optMem
  rw [storeMem_read_ne (by rw [e2]; omega), storeMem_read_ne (by rw [e1]; omega)]

/-- The option variables are readable and writable (`ShaRw`), as a span. -/
theorem shaRw_perm {b : Word} {m : Memory} (hb : b.toNat + 0xa188 < 2 ^ 64) (h : ShaRw b m)
    {acc : Access} (hacc : acc = .read ∨ acc = .write) {o n : Nat} (ho : o + n ≤ 0x28) :
    m.Permitted acc (b + BitVec.ofNat 64 (0xa160 + o)).toNat n := by
  rw [addr_toNat (by omega), Memory.Permitted, Memory.checkSpan_iff]
  simp only [Silmaril.Process.addressLimit]
  refine ⟨by omega, by omega, fun k hk => ?_⟩
  have := h (o + k) (by omega)
  rw [show b.toNat + (0xa160 + o) + k = b.toNat + 0xa160 + (o + k) by omega]
  rcases hacc with rfl | rfl
  · exact this.1
  · exact this.2

/-- A flag byte of `.bss` (`0xa170`–`0xa174`) after the option stores. -/
theorem flag_load {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m : Memory}
    (hf : m.readBytes (b + 0xa170#64).toNat 5 = some [0#8, 0#8, 0#8, 0#8, 0#8]) {i : Nat} (hi : i < 5) :
    loadN (optMem m b) (b + BitVec.ofNat 64 (0xa170 + i)) 1 = some 0#64 := by
  have e0 : (b + 0xa170#64).toNat = b.toNat + 0xa170 := addr_toNat (v := 0xa170) (by omega)
  have ei : (b + BitVec.ofNat 64 (0xa170 + i)).toNat = b.toNat + 0xa170 + i := by
    rw [addr_toNat (by omega)]; omega
  have h := Memory.readBytes_sub_range hf (offset := i) (len := 1) hi (by omega)
  rw [e0] at h
  have h' : (optMem m b).readBytes (b.toNat + 0xa170 + i) 1 = _ :=
    (optMem_rb hb m (a := b.toNat + 0xa170 + i) (n := 1) (by omega)).trans h
  rw [loadN_rb ei h']
  interval_cases i <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`main`'s option checks** (`0x29fd` → `0x2ae3`), stdin tier. -/
theorem tail_opts {W : World} {b lb sr : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {z : PState} (hd : z.g.done = none) (hMA : ShaMainAll b z.m.memory)
    (hM : ShaMemM b lb sr z.m.memory) (hrw : ShaRw b z.m.memory) (hrip : z.m.core.rip = b + 0x29fd#64)
    (hbin : loadN z.m.memory (z.m.core.read .rbp + 0xffffffffffffff38#64) 4 = some 0xffffffff#64)
    (hbin' : loadN (optMem z.m.memory b) (z.m.core.read .rbp + 0xffffffffffffff38#64) 4 = some 0xffffffff#64)
    (hchk : loadN (optMem z.m.memory b) (z.m.core.read .rbp + 0xffffffffffffff20#64) 1 = some 0#64)
    (k : ∀ y, y.m.core.rip = b + 0x2ae3#64 → y.m.memory = optMem z.m.memory b → y.g = z.g →
      (∀ r, r ≠ .rax → r ≠ .rdx → y.m.core.read r = z.m.core.read r) → y.m.core.read .rdx = 1#64 →
      y.m.core.fsBase = z.m.core.fsBase → MustQ W Q y) : MustQ W Q z := by
  have hkw : Keeps (ImgW b) z.m.memory (optMem z.m.memory b) := (optMem_keep hb _).mono fun _ h => Or.inl h
  have hMA1 : ShaMainAll b (optMem z.m.memory b) := hMA.keepW hb hkw
  have hM1 : ShaMemM b lb sr (optMem z.m.memory b) := hM.keepW hb hkw
  have hchk' : loadN (optMem z.m.memory b) (z.m.core.read .rbp + BitVec.signExtend 64 0xffffff20#32) 1 =
      some 0#64 := by
    rw [show BitVec.signExtend 64 0xffffff20#32 = 0xffffffffffffff20#64 from rfl]; exact hchk
  have hfl : z.m.memory.readBytes (b + 0xa170#64).toNat 5 = some [0#8, 0#8, 0#8, 0#8, 0#8] := hM.flags
  refine step29fd I hb hd hMA hrip hbin ?_ ?_ ?_
  · rw [hrip, show b + 0x29fd#64 + 0x776b#64 = b + BitVec.ofNat 64 (0xa160 + 8) by rw [BitVec.add_assoc]; rfl]
    exact shaRw_perm hb hrw (Or.inr rfl) (by decide)
  · rw [hrip, show b + 0x29fd#64 + 0x777b#64 = b + BitVec.ofNat 64 (0xa160 + 0x18) by rw [BitVec.add_assoc]; rfl]
    exact shaRw_perm hb hrw (Or.inr rfl) (by decide)
  intro w1 r1 m1 g1 R1 f1
  have m1' : w1.m.memory = optMem z.m.memory b := by
    rw [m1, hrip, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hd1 : w1.g.done = none := by rw [g1]; exact hd
  refine step2a29 I hb hd1 (m1' ▸ hMA1) r1 ?_ ?_
  · rw [r1, m1', show b + 0x2a29#64 + 0x75f3#64 = b + 0xa01c#64 by rw [BitVec.add_assoc]; rfl]
    have e : (b + 0xa01c#64).toNat = b.toNat + 0xa01c := addr_toNat (v := 0xa01c) (by omega)
    have h' : (optMem z.m.memory b).readBytes (b.toNat + 0xa01c) 1 = some [0x0a#8] :=
      (optMem_rb hb _ (a := b.toNat + 0xa01c) (n := 1) (by omega)).trans (by rw [← e]; exact hM.delim)
    rw [loadN_rb e h']
    rfl
  intro w2 r2 m2 g2 R2 f2
  have m2' : w2.m.memory = optMem z.m.memory b := m2.trans m1'
  have hd2 : w2.g.done = none := by rw [g2]; exact hd1
  have b2 : w2.m.core.read .rbp = z.m.core.read .rbp := (R2 _).trans (R1 _)
  refine step2c96 I hb hd2 (m2' ▸ hMA1) r2 (by rw [m2', b2]; exact hchk) ?_
  intro w3 r3 m3 g3 R3 f3
  have m3' : w3.m.memory = optMem z.m.memory b := m3.trans m2'
  have hd3 : w3.g.done = none := by rw [g3]; exact hd2
  have b3 : w3.m.core.read .rbp = z.m.core.read .rbp := (R3 _).trans b2
  refine step2cb4 I hb hd3 (m3' ▸ hMA1) r3 (by rw [m3', b3]; exact hbin') ?_
  intro w4 r4 m4 g4 R4 f4
  have m4' : w4.m.memory = optMem z.m.memory b := m4.trans m3'
  have hd4 : w4.g.done = none := by rw [g4]; exact hd3
  refine step2a4f I hb hd4 (m4' ▸ hMA1) r4 ?_ ?_
  · rw [r4, m4', show b + 0x2a4f#64 + 0x7722#64 = b + BitVec.ofNat 64 (0xa170 + 1) by rw [BitVec.add_assoc]; rfl]
    exact flag_load hb hfl (by decide)
  intro w5 r5 m5 g5 R5 f5
  have m5' : w5.m.memory = optMem z.m.memory b := m5.trans m4'
  have hd5 : w5.g.done = none := by rw [g5]; exact hd4
  refine step2a71 I hb hd5 (m5' ▸ hMA1) r5 ?_ ?_
  · rw [r5, m5', show b + 0x2a71#64 + 0x7703#64 = b + BitVec.ofNat 64 (0xa170 + 4) by rw [BitVec.add_assoc]; rfl]
    exact flag_load hb hfl (by decide)
  intro w6 r6 m6 g6 R6 f6
  have m6' : w6.m.memory = optMem z.m.memory b := m6.trans m5'
  have hd6 : w6.g.done = none := by rw [g6]; exact hd5
  refine step2a93 I hb hd6 (m6' ▸ hMA1) r6 ?_ ?_
  · rw [r6, m6', show b + 0x2a93#64 + 0x76e0#64 = b + BitVec.ofNat 64 (0xa170 + 3) by rw [BitVec.add_assoc]; rfl]
    exact flag_load hb hfl (by decide)
  intro w7 r7 m7 g7 R7 f7
  have m7' : w7.m.memory = optMem z.m.memory b := m7.trans m6'
  have hd7 : w7.g.done = none := by rw [g7]; exact hd6
  have b7 : w7.m.core.read .rbp = z.m.core.read .rbp :=
    (R7 _).trans ((R6 _).trans ((R5 _).trans ((R4 _).trans b3)))
  refine step2ab5 I hb hd7 (m7' ▸ hMA1) r7 ?_ ?_
  · rw [r7, m7', show b + 0x2ab5#64 + 0x76bd#64 = b + BitVec.ofNat 64 (0xa170 + 2) by rw [BitVec.add_assoc]; rfl]
    exact flag_load hb hfl (by decide)
  intro w8 r8 m8 g8 R8 a8 f8
  have m8' : w8.m.memory = optMem z.m.memory b := m8.trans m7'
  have hd8 : w8.g.done = none := by rw [g8]; exact hd7
  have b8 : w8.m.core.read .rbp = z.m.core.read .rbp := (R8 _ (by decide)).trans b7
  refine gap2abf I hb hd8 (m8' ▸ hM1.mainC) r8 a8 (by rw [m8', b8]; exact hchk') ?_
  intro w9 r9 m9 g9 R9 a9 z9 f9
  have m9' : w9.m.memory = optMem z.m.memory b := m9.trans m8'
  have hd9 : w9.g.done = none := by rw [g9]; exact hd8
  refine step2ac5 I hb hd9 (m9' ▸ hMA1) r9 a9 z9 ?_
  intro w10 r10 m10 g10 R10 d10 f10
  have m10' : w10.m.memory = optMem z.m.memory b := m10.trans m9'
  have hd10 : w10.g.done = none := by rw [g10]; exact hd9
  have b10 : w10.m.core.read .rbp = z.m.core.read .rbp :=
    (R10 _ (by decide)).trans ((R9 _ (by decide)).trans b8)
  refine step2acd I hb hd10 (m10' ▸ hMA1) r10 (by rw [m10', b10]; exact hchk) ?_
  intro w11 r11 m11 g11 R11 a11 f11
  have m11' : w11.m.memory = optMem z.m.memory b := m11.trans m10'
  have hd11 : w11.g.done = none := by rw [g11]; exact hd10
  refine gap2ad7 I hb hd11 (m11' ▸ hM1.mainC) r11 a11 ?_ ?_
  · rw [r11, m11', show b + 0x2ad7#64 + BitVec.ofNat 64 6 + BitVec.signExtend 64 0x7693#32 =
      b + BitVec.ofNat 64 (0xa170 + 0) by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact flag_load hb hfl (by decide)
  intro w12 r12 m12 g12 R12 a12 z12 f12
  have m12' : w12.m.memory = optMem z.m.memory b := m12.trans m11'
  have hd12 : w12.g.done = none := by rw [g12]; exact hd11
  refine step2add I hb hd12 (m12' ▸ hMA1) r12 z12 ?_
  intro w13 r13 m13 g13 R13 f13
  refine k w13 r13 (m13.trans m12') ?_ ?_ ?_ ?_
  · rw [g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1]
  · intro r ha hd
    rw [R13, R12 r ha, R11 r ha, R10 r hd, R9 r ha, R8 r ha, R7, R6, R5, R4, R3, R2, R1]
  · rw [R13, R12 _ (by decide), R11 _ (by decide)]; exact d10
  · rw [f13, f12, f11, f10, f9, f8, f7, f6, f5, f4, f3, f2, f1]

end Silmaril.Elf.Link.Dyn.Sha256sum
