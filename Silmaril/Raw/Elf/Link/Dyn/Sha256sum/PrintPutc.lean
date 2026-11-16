module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemPrint
public import Silmaril.Raw.Elf.Link.Dyn.Streams.Rep
public import Silmaril.Elf.Link.Dyn.Streams.Extra
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CloseStdout

/-! # sha256sum's output path, part (a): the inline `putc` on a stream

`putc_fast`: the fast path of glibc's `putc_unlocked` macro as compiled (load `_IO_write_ptr`,
compare with `_IO_write_end`, store the advanced pointer, store the byte) appends the byte to the
stream's buffer, writes only the stream's footprint, and keeps the mapping. It instantiates the
`StreamRep.putc` law with the two stores the machine actually performs.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (loadN storeN)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams

theorem permitted_of_loadN {m : Memory} {a : Word} {k : Nat} {v : Word} (h : loadN m a k = some v) :
    m.Permitted .read a.toNat k := by
  unfold loadN Memory.readBytes Memory.readWith at h
  split at h
  · rename_i hc; exact hc
  · cases h

theorem setWidth_byte (v : Word) : BitVec.ofNat 64 (v.toNat % 2 ^ (8 * 1)) = (v.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

/-- **The fast path of an inline `putc`** of the low byte of `v`: after storing `p + 1` into
`_IO_write_ptr` and `v`'s low byte at `p`, the stream has that byte appended to its buffer.
(`p` outside the pointer word and readable: `PutcLaw`.) -/
theorem putc_fast {S : StreamRep} {m m1 m2 : Memory} {f p e v : Word} {st : St}
    (hf : S.file m f st) (hp : loadN m (f + 0x28#64) 8 = some p) (he : loadN m (f + 0x30#64) 8 = some e)
    (hlt : p.toNat < e.toNat)
    (hdis : p.toNat + 1 ≤ (f + 0x28#64).toNat ∨ (f + 0x28#64).toNat + 8 ≤ p.toNat)
    (hpr : m.Permitted .read p.toNat 1) (hfw : f.toNat + 0x38 < 2 ^ 64)
    (h1 : storeN m (f + 0x28#64) 8 (p + 1#64) = some m1) (h2 : storeN m1 p 1 v = some m2) :
    S.file m2 f { st with buf := st.buf ++ [v.setWidth 8] } ∧ Keeps (fun a => ¬ S.foot m f a) m m2 ∧
      m2.regions = m.regions := by
  obtain ⟨hfp, -, -, hlaw⟩ := S.putc m f st p e (v.setWidth 8) hf hp he hlt
  have hfoot := (S.ptrs m f st hf).2.2
  have w1 := Silmaril.X86.Ext.storeN_writesOnly h1
  have w2 := Silmaril.X86.Ext.storeN_writesOnly h2
  have hreg : m2.regions = m.regions := w2.1.trans w1.1
  have hpr1 : m1.Permitted .read p.toNat 1 := by
    unfold Memory.Permitted at hpr ⊢; rw [Silmaril.X86.Memory.checkSpan_congr w1.1]; exact hpr
  have hlp : loadN m2 p 1 = some ((v.setWidth 8).setWidth 64) := by
    rw [Silmaril.X86.Ext.loadN_storeN h2 hpr1, setWidth_byte]
  have hlq : loadN m2 (f + 0x28#64) 8 = some (p + 1#64) := by
    rw [Silmaril.X86.Ext.loadN_storeN_disjoint h2 hdis.symm]
    exact Silmaril.X86.Ext.loadN_storeN_eight h1 (permitted_of_loadN hp)
  have hf8 : (f + 0x28#64).toNat = f.toNat + 0x28 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]; rfl
  have hk : Keeps (fun a => S.foot m f a ∧ a ≠ p.toNat ∧
      ¬ ((f + 0x28#64).toNat ≤ a ∧ a < (f + 0x28#64).toNat + 8)) m m2 :=
    (keeps_of_writesOnly w1 fun x hx => by
      by_contra hc; exact hx.2.2 ⟨by omega, by omega⟩).trans
    (keeps_of_writesOnly w2 fun x hx => by omega)
  refine ⟨hlaw m2 hk hreg hlp hlq, ?_, hreg⟩
  refine (keeps_of_writesOnly w1 fun x hx => ?_).trans (keeps_of_writesOnly w2 fun x hx => ?_)
  · by_contra hc; exact hx (hfoot x (by omega) (by omega))
  · by_contra hc
    have : x = p.toNat := by omega
    exact hx (this ▸ hfp)

theorem ShaMemP.keep {b lb sc : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemP b lb sc m) (h : Keeps (ShaImg b) m m') : ShaMemP b lb sc m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hm
  have l1 := shaC_lens.1
  obtain ⟨l2, l3, l4, l5⟩ := shaP_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa188 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨by omega, by omega⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Silmaril.X86.Ext.Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h1
  · unfold Silmaril.X86.Ext.Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h2
  · unfold Silmaril.X86.Ext.Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h3
  · unfold Silmaril.X86.Ext.Loaded Memory.fetchBytes at h4 ⊢
    rw [l4] at h4 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h4
  · unfold Silmaril.X86.Ext.Loaded Memory.fetchBytes at h5 ⊢
    rw [l5] at h5 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h5
  · unfold Memory.readBytes at h6 ⊢
    rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h6
  · unfold Memory.readBytes at h7 ⊢
    rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h7
  · exact (hl (off := 0x9dd8) (by decide)).trans h8
  · exact (hl (off := 0x9ef8) (by decide)).trans h9
  · exact (hl (off := 0x9f70) (by decide)).trans h10
  · exact (hl (off := 0x9f98) (by decide)).trans h11
  · exact (hl (off := 0x9df0) (by decide)).trans h12

theorem shaMemP_keep {b lb sc : Word} {W : World} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64) :
    ∀ m m', ShaMemP b lb sc m → Keeps W.InImage m m' → ShaMemP b lb sc m' :=
  fun _ _ hm h => hm.keep hb (by rw [I] at h; exact h)

/-- The imports the output path calls, bound eagerly (`sc`: the `strcspn` ifunc's choice). -/
structure PrintImps (E : Env) (W : World) (b lb sc : Word) : Prop where
  lz : W.lazy = none
  img : W.InImage = ShaImg b
  hb : b.toNat + 0xa188 < 2 ^ 64
  printf : ImpOk W (lb + 0x137bf0#64) (nm "__printf_chk") (printfHexStep E W)
  overflow : ImpOk W (lb + 0x95120#64) (nm "__overflow") (overflowStep E W)
  fputs : ImpOk W (lb + 0x91890#64) (nm "fputs_unlocked") (fputsStep E W)
  strcspn : ImpOk W sc (nm "strcspn") (strcspnStep E W)

/-- The stronger `putc` law the output path needs (a strengthening of `StreamRep.putc`): below `_IO_write_end` the
byte at `_IO_write_ptr` is also readable and outside the `FILE` header; the `FILE` does not wrap.

Second clause: **a client's store into a stream's footprint does not change which memory is the
library's** (keeping the mapping). Privacy is ownership, not contents: the inline `putc` macro
writes bytes the library owns (the buffer and `_IO_write_ptr`) without allocating or releasing
anything, so glibc's private memory (its data, heap and streams) is the same set afterwards. -/
def PutcLaw (E : Env) : Prop :=
  (∀ m f st p e, E.S.file m f st → loadN m (f + 0x28#64) 8 = some p →
    loadN m (f + 0x30#64) 8 = some e → p.toNat < e.toNat →
    m.Permitted .read p.toNat 1 ∧ (p.toNat + 1 ≤ (f + 0x28#64).toNat ∨ (f + 0x28#64).toNat + 8 ≤ p.toNat)) ∧
  ∀ m m' f st, E.S.file m f st → Keeps (fun a => ¬ E.S.foot m f a) m m' → m'.regions = m.regions →
    E.S.priv m' = E.S.priv m

/-- **An inline `putc` keeps `LibK`**: it writes only the stream's footprint (private memory, so
no library variable) and, by `PutcLaw`, leaves the private memory as it was. -/
theorem LibK.putc {E : Env} {W : World} (hP : PutcLaw E) {m0 m m' : Memory} {f : Word} {st : St}
    (h : LibK E W m0 m) (hf : E.S.file m f st) (hk : Keeps (fun a => ¬ E.S.foot m f a) m m')
    (hr : m'.regions = m.regions) : LibK E W m0 m' := by
  have hp := hP.2 m m' f st hf hk hr
  exact h.lib (fp := fun _ => False) (hk.mono fun a ha hfa => ha.1 (E.S.foot_priv _ _ _ _ hf hfa))
    (fun a ha => Or.inl (by rw [hp] at ha; exact ha)) (fun _ _ h => h)

/-- Distinct streams own disjoint bytes (a law the inline `putc` fast path needs to keep the
other streams: it writes only `stdout`'s own bytes). -/
def StreamsDisj (E : Env) : Prop :=
  ∀ m f f' st st' a, f ≠ f' → E.S.file m f st → E.S.file m f' st' → E.S.foot m f a → ¬ E.S.foot m f' a

/-! ## Instruction semantics on an abstract state (no `simp` on memory) -/

theorem exec_cmpq_rdi (c : Silmaril.X86.State) (m : Memory) (l : Nat) (d : BitVec 32) (v : Word)
    (h : Silmaril.X86.Ext.loadN m (c.read .rdi + d.signExtend 64) 8 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.aluR .q .cmp .rax (.mem (.ofReg .rdi none d))))) c m l =
      .ok { c with flags := Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp (c.read .rax) v, rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readRM, h, Silmaril.X86.Ext.aluStepR, ofReg_addr, Silmaril.X86.Ext.Sz.bytes]
theorem exec_storeq_rdi (c : Silmaril.X86.State) (m m' : Memory) (l : Nat) (d : BitVec 32)
    (h : Silmaril.X86.Ext.storeN m (c.read .rdi + d.signExtend 64) 8 (c.read .rdx) = some m') :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.mov .q (.mem (.ofReg .rdi none d)) .rdx))) c m l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l } m' := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM, h, ofReg_addr, Silmaril.X86.Ext.Sz.bytes]
theorem exec_storeb_imm (c : Silmaril.X86.State) (m m' : Memory) (l : Nat) (i : BitVec 8)
    (h : Silmaril.X86.Ext.storeN m (c.read .rax) 1 (i.setWidth 64) = some m') :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.movI8 (.mem (.ofReg .rax none 0#32)) i))) c m l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l } m' := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM8, ofReg_addr, h]

theorem exec_movzb_rbp (dst : Silmaril.X86.Reg) (c : Silmaril.X86.State) (m : Memory) (l : Nat) (d : BitVec 32) (v : Word)
    (h : Silmaril.X86.Ext.loadN m (c.read .rbp + d.signExtend 64) 1 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.movx false .d .b dst (.mem (.ofReg .rbp none d))))) c m l =
      .ok { c.write dst (((v.setWidth 8).setWidth 32).setWidth 64) with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readNarrow, h, ofReg_addr, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits,
    Silmaril.X86.Ext.Sz.write]
theorem exec_storeb_reg (r : Silmaril.X86.Reg) (c : Silmaril.X86.State) (m m' : Memory) (l : Nat)
    (h : Silmaril.X86.Ext.storeN m (c.read .rax) 1 (((c.read r).setWidth 8).setWidth 64) = some m') :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.store .b (.mem (.ofReg .rax none 0#32)) r))) c m l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l } m' := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeNarrow, ofReg_addr, h, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits]

theorem exec_cmpd0_rbp (c : Silmaril.X86.State) (m : Memory) (l : Nat) (d : BitVec 32) (v : Word)
    (h : Silmaril.X86.Ext.loadN m (c.read .rbp + d.signExtend 64) 4 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.aluI8 .d .cmp (.mem (.ofReg .rbp none d)) 0#8))) c m l =
      .ok { c with flags := Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp (v.setWidth 32) 0#32, rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readRM, h, ofReg_addr, Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.aluStep]

theorem exec_movzb_idx (c : Silmaril.X86.State) (m : Memory) (l : Nat) (v : Word)
    (h : Silmaril.X86.Ext.loadN m (c.read .rbx + c.read .r13) 1 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.movx false .d .b .rdx (.mem (.ofReg .rbx (some ⟨.r13, 0#2, by decide⟩) 0#32))))) c m l =
      .ok { c.write .rdx (((v.setWidth 8).setWidth 32).setWidth 64) with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits,
    Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Base.value, Silmaril.X86.Ext.Index.value, h]
theorem eval_b_sub (x y : BitVec 64) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .b = some (decide (x.toNat < y.toNat)) := by
  simp only [Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.Cond.eval]
  rw [Silmaril.X86.Ext.subBorrowN_eq (w := 63) x y]
  simp [BitVec.ult]

theorem exec_cmpb0_idx (c : Silmaril.X86.State) (m : Memory) (l : Nat) (v : Word)
    (h : Silmaril.X86.Ext.loadN m (c.read .r12 + c.read .rax) 1 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.cmpI8 (.mem (.ofReg .r12 (some ⟨.rax, 0#2, by decide⟩) 0#32)) 0#8))) c m l =
      .ok { c with flags := Silmaril.X86.Ext.subFlagsN (v.setWidth 8) 0#8, rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Base.value,
    Silmaril.X86.Ext.Index.value, h]

end Silmaril.Elf.Link.Dyn.Sha256sum
