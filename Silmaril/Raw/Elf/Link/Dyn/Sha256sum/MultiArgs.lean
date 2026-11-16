module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiBlocks

/-! # GNU `sha256sum FILE…`: the operand loop's set-up (`0x2ae3` → `0x2b81`)

`optind (= 1) != argc`: no `"-"` is stored; `r8 = &argv[1]` (below `&argv[argc]`),
`r12 = argv[1]` (saved at `rbp-0x100`), the loop's frame slots (`end = &argv[argc]`, the
`missing` byte's address, the `ok` byte), and the arguments of `digest_file (argv[1], …)` at
`0x2b81`. One lemma per block (`step2ae3n`, `step2b08`, `step2b15`, `step2b2c`, `step2b74`).
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

/-- The memory after `0x2ae3`–`0x2b74` with operands: the saved name (`p1`) and the loop's
frame slots (`fp`: `rbp`; `e`: the end of `argv`; `dl`: the `ok` flag in `rdx`). -/
def filesMem (m : Memory) (fp p1 e dl : Word) : Memory :=
  storeMem (storeMem (storeMem (storeMem m (fp + 0xffffffffffffff00#64) 8 p1)
    (fp + 0xffffffffffffff18#64) 8 e) (fp + 0xffffffffffffff20#64) 8 (fp + 0xffffffffffffff58#64))
    (fp + 0xffffffffffffff28#64) 1 ((dl.setWidth 8).setWidth 64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Operands: the loop's set-up** (`0x2ae3` → `0x2b81`). -/
theorem multi_args {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {y : PState} (hd : y.g.done = none)
    (hMA : ∀ m, Keeps (ShaImg b) y.m.memory m → ShaMainAll b m)
    (hrip : y.m.core.rip = b + 0x2ae3#64) {A : Word}
    (hgot : loadN y.m.memory (b + 0x9fc8#64) 8 = some A) (hopt : loadN y.m.memory A 4 = some 1#64)
    {n : BitVec 32} (hr12 : BitVec.setWidth 32 (y.m.core.read .r12) = n) (hn : n ≠ 1#32)
    (hlt : (y.m.core.read .rbx + 8#64).ult (y.m.core.read .rbx + (n.signExtend 64 <<< 3)) = true)
    {p1 : Word} (hp1 : loadN y.m.memory (y.m.core.read .rbx + 8#64) 8 = some p1)
    (hfp : 0x100 ≤ (y.m.core.read .rbp).toNat)
    (hfI : ∀ x, ShaImg b x → x < (y.m.core.read .rbp).toNat - 0x100 ∨ (y.m.core.read .rbp).toNat ≤ x)
    (hfr : ∀ x, (y.m.core.read .rbp).toNat - 0x100 ≤ x → x < (y.m.core.read .rbp).toNat →
      y.m.memory.permits .read x = true ∧ y.m.memory.permits .write x = true)
    (hchk : loadN y.m.memory (y.m.core.read .rbp + 0xffffffffffffff20#64) 1 = some 0#64)
    (k : ∀ v, v.m.core.rip = b + 0x2b81#64 →
      v.m.memory = filesMem y.m.memory (y.m.core.read .rbp) p1
        (y.m.core.read .rbx + (n.signExtend 64 <<< 3)) (y.m.core.read .rdx) →
      v.g = y.g → v.m.core.fsBase = y.m.core.fsBase →
      v.m.core.read .rdi = p1 → v.m.core.read .r12 = p1 →
      v.m.core.read .rsi = y.m.core.read .rbp + 0xffffffffffffffa0#64 →
      v.m.core.read .rbx = y.m.core.read .rbp + 0xffffffffffffffa0#64 →
      v.m.core.read .rdx = y.m.core.read .rbp + 0xffffffffffffff58#64 →
      v.m.core.read .r14 = b + 0x7238#64 → v.m.core.read .r15 = y.m.core.read .rbx + 8#64 →
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .r8 → r ≠ .r12 → r ≠ .rbx → r ≠ .r14 → r ≠ .r15 →
        r ≠ .rdx → r ≠ .rsi → v.m.core.read r = y.m.core.read r) → MustQ W Q v) : MustQ W Q y := by
  have hMA0 : ShaMainAll b y.m.memory := hMA _ (Keeps.refl _ _)
  have e00 := fpo00 _ hfp
  have e18 := fpo18 _ hfp
  have e20 := fpo20 _ hfp
  have e28 := fpo28 _ hfp
  have hfrR : ∀ x, (y.m.core.read .rbp).toNat - 0x100 ≤ x → x < (y.m.core.read .rbp).toNat →
      y.m.memory.permits .read x = true := fun x h1 h2 => (hfr x h1 h2).1
  have hfrW : ∀ x, (y.m.core.read .rbp).toNat - 0x100 ≤ x → x < (y.m.core.read .rbp).toNat →
      y.m.memory.permits .write x = true := fun x h1 h2 => (hfr x h1 h2).2
  have hlim : (y.m.core.read .rbp).toNat < 2 ^ 64 := (y.m.core.read .rbp).isLt
  have kI : ∀ (m : Memory) (a : Word) (k : Nat) (v : Word), (y.m.core.read .rbp).toNat - 0x100 ≤ a.toNat →
      a.toNat + k ≤ (y.m.core.read .rbp).toNat → Keeps (ShaImg b) m (storeMem m a k v) :=
    fun m a k v h1 h2 => keepsImg_store (lo := (y.m.core.read .rbp).toNat - 0x100)
      (hi := (y.m.core.read .rbp).toNat) h1 h2 hfI
  refine step2ae3n I hb hd hMA0 hrip (A := A)
    (by rw [hrip, show b + 0x2ae3#64 + 0x74e5#64 = b + 0x9fc8#64 by rw [BitVec.add_assoc]; rfl]; exact hgot)
    hopt hr12 hn ?_
  intro w1 r1 m1 g1 R1 a1 c1 f1
  have hd1 : w1.g.done = none := by rw [g1]; exact hd
  have bx1 : w1.m.core.read .rbx = y.m.core.read .rbx := R1 _ (by decide) (by decide)
  have bp1 : w1.m.core.read .rbp = y.m.core.read .rbp := R1 _ (by decide) (by decide)
  refine step2b08 I hb hd1 (m1 ▸ hMA0) r1 a1 (by rw [bx1, c1]; exact hlt) ?_
  intro w3 r3 m3 g3 R3 e3 f3
  have m3' : w3.m.memory = y.m.memory := m3.trans m1
  have hd3 : w3.g.done = none := by rw [g3]; exact hd1
  have bp3 : w3.m.core.read .rbp = y.m.core.read .rbp := by rw [R3 _ (by decide)]; exact bp1
  have r8' : w3.m.core.read .r8 = y.m.core.read .rbx + 8#64 := by rw [e3, bx1]
  refine step2b15 I hb hd3 (m3' ▸ hMA0) r3 (nm := p1)
    (by rw [m3', r8']; exact hp1) (by rw [m3', bp3]; exact hchk)
    (by rw [m3', bp3]; exact perm_span hfrW (by omega) (by omega) hlim) ?_
  intro w4 r4 m4 g4 R4 n4 f4
  have hd4 : w4.g.done = none := by rw [g4]; exact hd3
  have bp4 : w4.m.core.read .rbp = y.m.core.read .rbp := by rw [R4 _ (by decide)]; exact bp3
  have cx4 : w4.m.core.read .rcx = y.m.core.read .rbx + (n.signExtend 64 <<< 3) := by
    rw [R4 _ (by decide), R3 _ (by decide), c1]
  have m4' : w4.m.memory = storeMem y.m.memory (y.m.core.read .rbp + 0xffffffffffffff00#64) 8 p1 := by
    rw [m4, m3', bp3]
  have k1 : Keeps (ShaImg b) y.m.memory (storeMem y.m.memory (y.m.core.read .rbp + 0xffffffffffffff00#64) 8 p1) :=
    kI _ _ _ _ (by omega) (by omega)
  refine step2b2c I hb hd4 (m4' ▸ hMA _ k1) r4
    (by rw [m4', bp4]; exact perm_span hfrW (by omega) (by omega) hlim)
    (by rw [m4', bp4]; exact perm_span hfrW (by omega) (by omega) hlim)
    (by rw [m4', bp4]; exact perm_span hfrW (by omega) (by omega) hlim) ?_
  intro w5 r5 m5 g5 R5 b5 t5 q5 f5
  have hd5 : w5.g.done = none := by rw [g5]; exact hd4
  have dx4 : w4.m.core.read .rdx = y.m.core.read .rdx := by
    rw [R4 _ (by decide), R3 _ (by decide), R1 _ (by decide) (by decide)]
  have m5' : w5.m.memory = filesMem y.m.memory (y.m.core.read .rbp) p1
      (y.m.core.read .rbx + (n.signExtend 64 <<< 3)) (y.m.core.read .rdx) := by
    rw [m5, m4', bp4, cx4, dx4]; rfl
  have k5 : Keeps (ShaImg b) y.m.memory (filesMem y.m.memory (y.m.core.read .rbp) p1
      (y.m.core.read .rbx + (n.signExtend 64 <<< 3)) (y.m.core.read .rdx)) := by
    unfold filesMem
    exact ((k1.trans (kI _ _ _ _ (by omega) (by omega))).trans (kI _ _ _ _ (by omega) (by omega))).trans
      (kI _ _ _ _ (by omega) (by omega))
  have bp5 : w5.m.core.read .rbp = y.m.core.read .rbp := by
    rw [R5 _ (by decide) (by decide) (by decide) (by decide)]; exact bp4
  have hdx : loadN w5.m.memory (w5.m.core.read .rbp + 0xffffffffffffff20#64) 8 =
      some (y.m.core.read .rbp + 0xffffffffffffff58#64) := by
    rw [m5', bp5]; unfold filesMem
    rw [loadN_storeMem_ne (a := y.m.core.read .rbp + 0xffffffffffffff28#64)
      (A := y.m.core.read .rbp + 0xffffffffffffff20#64) (k := 1) (n := 8) (by rw [e20, e28]; omega)]
    exact loadN_store8 (perm_span hfrR (by omega) (by omega) hlim)
  refine step2b74 I hb hd5 (m5' ▸ hMA _ k5) r5 hdx ?_
  intro w6 r6 m6 g6 R6 d6 s6 i6 f6
  refine k w6 r6 (m6.trans m5') (by rw [g6, g5, g4, g3, g1]) (by rw [f6, f5, f4, f3, f1])
    ?_ ?_ ?_ ?_ d6 ?_ ?_ ?_
  · rw [i6, R5 _ (by decide) (by decide) (by decide) (by decide)]; exact n4
  · rw [R6 _ (by decide) (by decide) (by decide), R5 _ (by decide) (by decide) (by decide) (by decide)]; exact n4
  · rw [s6, b5, bp4]
  · rw [R6 _ (by decide) (by decide) (by decide), b5, bp4]
  · rw [R6 _ (by decide) (by decide) (by decide), t5, r4, BitVec.add_assoc]; rfl
  · rw [R6 _ (by decide) (by decide) (by decide), q5, R4 _ (by decide), r8']
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    rw [R6 r h9 h10 h3, R5 r h1 h6 h7 h8, R4 r h5, R3 r h4, R1 r h1 h2]

end Silmaril.Elf.Link.Dyn.Sha256sum
