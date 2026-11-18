module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailRun1
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailArgs

/-! # GNU `sha256sum`, stdin tier: `main` from `0x2ae3` to the call of `digest_file` (`0x2b81`)

`tail_args` chains the blocks of `TailArgs`: `optind == argc` (no operand), so `argv[argc]`
becomes `"-"` (`b + 0x716e`), and the loop's slots are set up (`[rbp-0x100]` the name,
`[rbp-0xe8]` the end of the operands, `[rbp-0xe0]` the `missing` byte's address, `[rbp-0xd8]`
the `ok` byte); control reaches `call digest_file` with `rdi = "-"`, `rsi = rbp - 0x60` (the
digest) and `rdx = rbp - 0xa8` (`missing`). `argsMem` is the memory after these stores.
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

/-- The memory after `0x2ae3`–`0x2b74`: `argv[1] = "-"` (`av`: `argv`), and the loop's frame
slots (`fp`: `rbp`; `dl`: the `ok` flag in `rdx`). -/
def argsMem (m : Memory) (av fp b dl : Word) : Memory :=
  storeMem (storeMem (storeMem (storeMem (storeMem m (av + 8#64) 8 (b + 0x716e#64))
    (fp + 0xffffffffffffff00#64) 8 (b + 0x716e#64)) (fp + 0xffffffffffffff18#64) 8 (av + 16#64))
    (fp + 0xffffffffffffff20#64) 8 (fp + 0xffffffffffffff58#64)) (fp + 0xffffffffffffff28#64) 1
    ((dl.setWidth 8).setWidth 64)

theorem loadN_store8 {m : Memory} {a v : Word} (hr : m.Permitted .read a.toNat 8) :
    loadN (storeMem m a 8 v) a 8 = some v := by
  simp only [loadN, storeMem_read hr, Option.map_some, Silmaril.X86.Ext.leValue_leBytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [v.isLt]

theorem ult_8_16 {av : Word} (h : av.toNat + 16 < 2 ^ 64) : (av + 8#64).ult (av + 8#64 + 8#64) = true := by
  have e1 : (av + 8#64).toNat = av.toNat + 8 := addr_toNat (v := 8) (by omega)
  have e2 : (av + 8#64 + 8#64).toNat = av.toNat + 16 := by
    rw [addr_toNat (v := 8) (by rw [e1]; omega), e1]
  simp only [BitVec.ult, e1, e2, decide_eq_true_eq]
  omega

/-- `fp + (2^64 - k)` is `fp - k` when `k ≤ fp`. -/
theorem neg_off {fp : Word} {k : Nat} (hk : k ≤ fp.toNat) (hk0 : 0 < k) (hk2 : k < 2 ^ 64) :
    (fp + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = fp.toNat - k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := fp.isLt
  rw [Nat.mod_eq_of_lt (a := 2 ^ 64 - k) (by omega)]
  omega

theorem keepsImg_store {b : Word} {m : Memory} {a : Word} {k : Nat} {v : Word} {lo hi : Nat}
    (hlo : lo ≤ a.toNat) (hhi : a.toNat + k ≤ hi) (hI : ∀ x, ShaImg b x → x < lo ∨ hi ≤ x) :
    Keeps (ShaImg b) m (storeMem m a k v) :=
  storeMem_keeps fun x hx => by rcases hI x hx with h | h <;> omega

theorem perm_span {m : Memory} {acc : Access} {lo hi a n : Nat}
    (hp : ∀ x, lo ≤ x → x < hi → m.permits acc x = true) (h1 : lo ≤ a) (h2 : a + n ≤ hi)
    (hlim : hi < 2 ^ 64) : m.Permitted acc a n := by
  rw [Memory.Permitted, Memory.checkSpan_iff]
  simp only [Silmaril.Process.addressLimit]
  exact ⟨by omega, by omega, fun k hk => hp _ (by omega) (by omega)⟩

theorem fpo00 (fp : Word) (h : 0x100 ≤ fp.toNat) : (fp + 0xffffffffffffff00#64).toNat = fp.toNat - 0x100 :=
  neg_off (k := 0x100) h (by decide) (by decide)
theorem fpo18 (fp : Word) (h : 0x100 ≤ fp.toNat) : (fp + 0xffffffffffffff18#64).toNat = fp.toNat - 0xe8 :=
  neg_off (k := 0xe8) (by omega) (by decide) (by decide)
theorem fpo20 (fp : Word) (h : 0x100 ≤ fp.toNat) : (fp + 0xffffffffffffff20#64).toNat = fp.toNat - 0xe0 :=
  neg_off (k := 0xe0) (by omega) (by decide) (by decide)
theorem fpo28 (fp : Word) (h : 0x100 ≤ fp.toNat) : (fp + 0xffffffffffffff28#64).toNat = fp.toNat - 0xd8 :=
  neg_off (k := 0xd8) (by omega) (by decide) (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **No operand: `"-"`, and the loop's set-up** (`0x2ae3` → `0x2b81`). -/
theorem tail_args {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {y : PState} (hd : y.g.done = none)
    (hMA : ∀ m, Keeps (ShaImg b) y.m.memory m → ShaMainAll b m)
    (hrip : y.m.core.rip = b + 0x2ae3#64) {A : Word}
    (hgot : loadN y.m.memory (b + 0x9fc8#64) 8 = some A) (hopt : loadN y.m.memory A 4 = some 1#64)
    (hr12 : BitVec.setWidth 32 (y.m.core.read .r12) = 1#32)
    (hav : (y.m.core.read .rbx).toNat + 16 < 2 ^ 64)
    (hwa : y.m.memory.Permitted .write (y.m.core.read .rbx + 8#64).toNat 8)
    (hra : y.m.memory.Permitted .read (y.m.core.read .rbx + 8#64).toNat 8)
    (hfp : 0x100 ≤ (y.m.core.read .rbp).toNat)
    (hfI : ∀ x, ShaImg b x → x < (y.m.core.read .rbp).toNat - 0x100 ∨ (y.m.core.read .rbp).toNat ≤ x)
    (haI : ∀ x, ShaImg b x → x < (y.m.core.read .rbx).toNat + 8 ∨ (y.m.core.read .rbx).toNat + 16 ≤ x)
    (haF : (y.m.core.read .rbp).toNat ≤ (y.m.core.read .rbx).toNat)
    (hfr : ∀ x, (y.m.core.read .rbp).toNat - 0x100 ≤ x → x < (y.m.core.read .rbp).toNat →
      y.m.memory.permits .read x = true ∧ y.m.memory.permits .write x = true)
    (hchk : loadN y.m.memory (y.m.core.read .rbp + 0xffffffffffffff20#64) 1 = some 0#64)
    (k : ∀ v, v.m.core.rip = b + 0x2b81#64 →
      v.m.memory = argsMem y.m.memory (y.m.core.read .rbx) (y.m.core.read .rbp) b (y.m.core.read .rdx) →
      v.g = y.g → v.m.core.fsBase = y.m.core.fsBase →
      v.m.core.read .rdi = b + 0x716e#64 → v.m.core.read .r12 = b + 0x716e#64 →
      v.m.core.read .rsi = y.m.core.read .rbp + 0xffffffffffffffa0#64 →
      v.m.core.read .rbx = y.m.core.read .rbp + 0xffffffffffffffa0#64 →
      v.m.core.read .rdx = y.m.core.read .rbp + 0xffffffffffffff58#64 →
      v.m.core.read .r14 = b + 0x7238#64 → v.m.core.read .r15 = y.m.core.read .rbx + 8#64 →
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .r8 → r ≠ .r12 → r ≠ .rbx → r ≠ .r14 → r ≠ .r15 →
        r ≠ .rdx → r ≠ .rsi → v.m.core.read r = y.m.core.read r) → MustQ W Q v) : MustQ W Q y := by
  have hMA0 : ShaMainAll b y.m.memory := hMA _ (Keeps.refl _ _)
  have ea : (y.m.core.read .rbx + 8#64).toNat = (y.m.core.read .rbx).toNat + 8 := addr_toNat (v := 8) (by omega)
  have e00 := fpo00 _ hfp
  have e18 := fpo18 _ hfp
  have e20 := fpo20 _ hfp
  have e28 := fpo28 _ hfp
  have hfrR : ∀ x, (y.m.core.read .rbp).toNat - 0x100 ≤ x → x < (y.m.core.read .rbp).toNat →
      y.m.memory.permits .read x = true := fun x h1 h2 => (hfr x h1 h2).1
  have hfrW : ∀ x, (y.m.core.read .rbp).toNat - 0x100 ≤ x → x < (y.m.core.read .rbp).toNat →
      y.m.memory.permits .write x = true := fun x h1 h2 => (hfr x h1 h2).2
  have hlim : (y.m.core.read .rbp).toNat < 2 ^ 64 := (y.m.core.read .rbp).isLt
  -- the memories along the way
  have k1 : Keeps (ShaImg b) y.m.memory (storeMem y.m.memory (y.m.core.read .rbx + 8#64) 8 (b + 0x716e#64)) :=
    keepsImg_store (lo := (y.m.core.read .rbx).toNat + 8) (hi := (y.m.core.read .rbx).toNat + 16)
      (by omega) (by omega) haI
  have k2 : Keeps (ShaImg b) (storeMem y.m.memory (y.m.core.read .rbx + 8#64) 8 (b + 0x716e#64))
      (storeMem (storeMem y.m.memory (y.m.core.read .rbx + 8#64) 8 (b + 0x716e#64))
        (y.m.core.read .rbp + 0xffffffffffffff00#64) 8 (b + 0x716e#64)) :=
    keepsImg_store (lo := (y.m.core.read .rbp).toNat - 0x100) (hi := (y.m.core.read .rbp).toNat)
      (by omega) (by omega) hfI
  have k5 : Keeps (ShaImg b) y.m.memory
      (argsMem y.m.memory (y.m.core.read .rbx) (y.m.core.read .rbp) b (y.m.core.read .rdx)) := by
    refine (k1.trans k2).trans ((keepsImg_store (lo := (y.m.core.read .rbp).toNat - 0x100)
      (hi := (y.m.core.read .rbp).toNat) (by omega) (by omega) hfI).trans
      ((keepsImg_store (lo := (y.m.core.read .rbp).toNat - 0x100)
      (hi := (y.m.core.read .rbp).toNat) (by omega) (by omega) hfI).trans
      (keepsImg_store (lo := (y.m.core.read .rbp).toNat - 0x100)
      (hi := (y.m.core.read .rbp).toNat) (by omega) (by omega) hfI)))
  refine step2ae3 I hb hd hMA0 hrip (A := A)
    (by rw [hrip, show b + 0x2ae3#64 + 0x74e5#64 = b + 0x9fc8#64 by rw [BitVec.add_assoc]; rfl]; exact hgot)
    hopt hr12 ?_
  intro w1 r1 m1 g1 R1 a1 c1 f1
  have hd1 : w1.g.done = none := by rw [g1]; exact hd
  have hs2 : w1.m.core.read .rcx + 0#64 = y.m.core.read .rbx + 8#64 := by
    rw [c1, BitVec.add_zero]
  refine step2af9 I hb hd1 (m1 ▸ hMA0) r1 (by rw [m1, hs2]; exact hwa) ?_
  intro w2 r2 m2 g2 R2 c2 d2 f2
  have hv2 : w1.m.core.rip + 0x4675#64 = b + 0x716e#64 := by rw [r1, BitVec.add_assoc]; rfl
  have m2' : w2.m.memory = storeMem y.m.memory (y.m.core.read .rbx + 8#64) 8 (b + 0x716e#64) := by
    rw [m2, m1, hs2, hv2]
  have hd2 : w2.g.done = none := by rw [g2]; exact hd1
  have bx2 : w2.m.core.read .rbx = y.m.core.read .rbx := by
    rw [R2 _ (by decide) (by decide), R1 _ (by decide) (by decide)]
  have bp2 : w2.m.core.read .rbp = y.m.core.read .rbp := by
    rw [R2 _ (by decide) (by decide), R1 _ (by decide) (by decide)]
  have cx2 : w2.m.core.read .rcx = y.m.core.read .rbx + 8#64 + 8#64 := by
    rw [c2, c1]
  have hMA1 : ShaMainAll b (storeMem y.m.memory (y.m.core.read .rbx + 8#64) 8 (b + 0x716e#64)) := hMA _ k1
  refine step2b08 I hb hd2 (m2' ▸ hMA1) r2
    (by rw [R2 _ (by decide) (by decide)]; exact a1) (by rw [bx2, cx2]; exact ult_8_16 hav) ?_
  intro w3 r3 m3 g3 R3 e3 f3
  have m3' : w3.m.memory = storeMem y.m.memory (y.m.core.read .rbx + 8#64) 8 (b + 0x716e#64) := m3.trans m2'
  have hd3 : w3.g.done = none := by rw [g3]; exact hd2
  have bp3 : w3.m.core.read .rbp = y.m.core.read .rbp := by rw [R3 _ (by decide)]; exact bp2
  have r8' : w3.m.core.read .r8 = y.m.core.read .rbx + 8#64 := by rw [e3, bx2]
  have hchk1 : loadN (storeMem y.m.memory (y.m.core.read .rbx + 8#64) 8 (b + 0x716e#64))
      (y.m.core.read .rbp + 0xffffffffffffff20#64) 1 = some 0#64 := by
    rw [loadN_storeMem_ne (a := y.m.core.read .rbx + 8#64) (A := y.m.core.read .rbp + 0xffffffffffffff20#64)
      (k := 8) (n := 1) (by rw [ea, e20]; omega)]; exact hchk
  refine step2b15 I hb hd3 (m3' ▸ hMA1) r3 (nm := b + 0x716e#64)
    (by rw [m3', r8']; exact loadN_store8 hra) (by rw [m3', bp3]; exact hchk1)
    (by rw [m3', bp3]; exact perm_span hfrW (by omega) (by omega) hlim) ?_
  intro w4 r4 m4 g4 R4 n4 f4
  have hd4 : w4.g.done = none := by rw [g4]; exact hd3
  have bp4 : w4.m.core.read .rbp = y.m.core.read .rbp := by rw [R4 _ (by decide)]; exact bp3
  have cx4 : w4.m.core.read .rcx = y.m.core.read .rbx + 8#64 + 8#64 := by
    rw [R4 _ (by decide), R3 _ (by decide)]; exact cx2
  have m4' : w4.m.memory = storeMem (storeMem y.m.memory (y.m.core.read .rbx + 8#64) 8 (b + 0x716e#64))
      (y.m.core.read .rbp + 0xffffffffffffff00#64) 8 (b + 0x716e#64) := by
    rw [m4, m3', bp3]
  refine step2b2c I hb hd4 (m4' ▸ hMA _ (k1.trans k2)) r4
    (by rw [m4', bp4]; exact perm_span hfrW (by omega) (by omega) hlim)
    (by rw [m4', bp4]; exact perm_span hfrW (by omega) (by omega) hlim)
    (by rw [m4', bp4]; exact perm_span hfrW (by omega) (by omega) hlim) ?_
  intro w5 r5 m5 g5 R5 b5 t5 q5 f5
  have hd5 : w5.g.done = none := by rw [g5]; exact hd4
  have dx4 : w4.m.core.read .rdx = y.m.core.read .rdx := by
    rw [R4 _ (by decide), R3 _ (by decide), R2 _ (by decide) (by decide), R1 _ (by decide) (by decide)]
  have m5' : w5.m.memory = argsMem y.m.memory (y.m.core.read .rbx) (y.m.core.read .rbp) b (y.m.core.read .rdx) := by
    rw [m5, m4', bp4, cx4, dx4, BitVec.add_assoc]; rfl
  have bp5 : w5.m.core.read .rbp = y.m.core.read .rbp := by rw [R5 _ (by decide) (by decide) (by decide) (by decide)]; exact bp4
  have hdx : loadN w5.m.memory (w5.m.core.read .rbp + 0xffffffffffffff20#64) 8 =
      some (y.m.core.read .rbp + 0xffffffffffffff58#64) := by
    rw [m5', bp5]; unfold argsMem
    rw [loadN_storeMem_ne (a := y.m.core.read .rbp + 0xffffffffffffff28#64)
      (A := y.m.core.read .rbp + 0xffffffffffffff20#64) (k := 1) (n := 8) (by rw [e20, e28]; omega)]
    exact loadN_store8 (perm_span hfrR (by omega) (by omega) hlim)
  refine step2b74 I hb hd5 (m5' ▸ hMA _ k5) r5 hdx ?_
  intro w6 r6 m6 g6 R6 d6 s6 i6 f6
  refine k w6 r6 (m6.trans m5') (by rw [g6, g5, g4, g3, g2, g1]) (by rw [f6, f5, f4, f3, f2, f1])
    ?_ ?_ ?_ ?_ d6 ?_ ?_ ?_
  · rw [i6, R5 _ (by decide) (by decide) (by decide) (by decide)]; exact n4
  · rw [R6 _ (by decide) (by decide) (by decide), R5 _ (by decide) (by decide) (by decide) (by decide)]; exact n4
  · rw [s6, b5, bp4]
  · rw [R6 _ (by decide) (by decide) (by decide), b5, bp4]
  · rw [R6 _ (by decide) (by decide) (by decide), t5, r4, BitVec.add_assoc]; rfl
  · rw [R6 _ (by decide) (by decide) (by decide), q5, R4 _ (by decide), r8']
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    rw [R6 r h9 h10 h3, R5 r h1 h6 h7 h8, R4 r h5, R3 r h4, R2 r h2 h3, R1 r h1 h2]

end Silmaril.Elf.Link.Dyn.Sha256sum
