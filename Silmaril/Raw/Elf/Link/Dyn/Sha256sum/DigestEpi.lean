module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestDone

/-! # GNU `sha256sum`: `digest_file`'s return (`0x6b61` → `ret`)

```
0x6b61: eax = 1; check the stack guard (rbp - 0x38 against %fs:0x28); add rsp, 0xa8;
        pop rbx, r12, r13, r14, r15, rbp; ret
```
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

/-- `sub r64, r/m64` flags as the semantics builds them. -/
abbrev subQ (x y : BitVec 64) : Silmaril.X86.Flags :=
  @Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.Ext.Sz.q.bits Silmaril.X86.AluOp.sub x y

theorem eval_subQ (x y : BitVec 64) (c : Silmaril.X86.Ext.Cond) :
    Silmaril.X86.Ext.Cond.eval (subQ x y) c = some (Silmaril.X86.Ext.Cond.afterCmp (w := 63) x y c) :=
  Silmaril.X86.Ext.eval_subFlagsN (w := 63) x y c

/-- `sub r64, qword fs:[d]`. -/
theorem exec_subfs (dst : Reg) (d : BitVec 32) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : loadN m (c.fsBase + d.signExtend 64) 8 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.aluR .q .sub dst (.mem (Silmaril.X86.Ext.Mem.ofFs Option.none d))))) c m l =
      .ok ⟨c.regs.write dst (Silmaril.X86.Ext.AluOp.resultN Silmaril.X86.AluOp.sub (c.read dst) v),
        c.rip + BitVec.ofNat 64 l, subQ (c.read dst) v, c.fsBase⟩ m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofFs, Silmaril.X86.Ext.Base.value, h,
    Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.readRM, subQ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`digest_file` returns 1** (`0x6b61`): the guard intact, the six saved registers restored. -/
theorem dg_epi {E : Env} {W : World} {b lb kb : Word} (I : CloseImps E W b lb)
    {X : Nat → Prop} {Q : PState → Prop} {s u : PState} {g : Word}
    (hB : BodyX W (ShaMemCD b lb kb) s u 216 1024 (sv6 s) X) (hrip : u.m.core.rip = b + 0x6b61#64)
    (hrbp : u.m.core.read .rbp = s.m.core.read .rsp - 8#64)
    (hsg : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [g]))
    (habi : AbiEntry s.m.core s.m.memory)
    (hguard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j))
    (hX : ∀ x, X x → x + 1024 < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x)
    (hgX : ∀ j, j < 8 → ¬ X ((s.m.core.fsBase + 0x28#64).toNat + j))
    (k : ∀ t, AbiReturn s.m.core s.m.memory t.m.core → t.m.memory = u.m.memory → low32 (t.m.core.read .rax) = 1#32 →
      t.g = u.g → t.m.core.fsBase = s.m.core.fsBase → MustQ W Q t) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hroom := hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have hur : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by decide)
  have a64 : (u.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32).toNat = (s.m.core.read .rsp).toNat - 64 := by
    rw [hrbp, show BitVec.signExtend 64 0xffffffc8#32 = 0xffffffffffffffc8#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have hgu : loadN u.m.memory (u.m.core.fsBase + BitVec.signExtend 64 0x28#32) 8 = some g := by
    rw [hB.fs, show BitVec.signExtend 64 0x28#32 = 0x28#64 by decide,
      (hB.keepX.mono fun a (ha : W.Kept a ∧ ¬ X a) => ⟨Or.inl ha.1, ha.2⟩).loadN fun j hj => ⟨hgk j hj, hgX j hj⟩]
    exact hguard
  refine must_listed (o := 289) shaD_listing_ok.2.2 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrip, ripadd]) ?_
  xstep [hrip]
  refine must_listed (o := 294) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  rw [exec_loadqd _ _ _ _ _ _ _ (by
    show loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32) 8 = some g
    exact loadN_of_enc (by rw [a64]; exact hsg)), WP_ok]
  refine must_listed (o := 298) shaD_listing_ok.2.2 rfl hB.done (by simp only [ripadd]; exact hin _ (by decide))
    hB.mem.2.digestFile (by simp only [ripadd]) ?_
  rw [exec_subfs _ _ _ _ _ g (by show loadN u.m.memory (u.m.core.fsBase + BitVec.signExtend 64 0x28#32) 8 = some g; exact hgu),
    WP_ok]
  refine must_listed (o := 307) shaD_listing_ok.2.2 rfl hB.done (by simp only [ripadd]; exact hin _ (by decide))
    hB.mem.2.digestFile (by simp only [ripadd]) ?_
  have hne : Silmaril.X86.Ext.Cond.afterCmp (w := 63) g g .ne = false := by
    simp [Silmaril.X86.Ext.Cond.afterCmp]
  xstep [eval_subQ, hrip, hne]
  refine must_listed (o := 313) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  have sv : ∀ p ∈ sv6 s, u.m.memory.readBytes ((s.m.core.read .rsp).toNat - p.1) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [p.2]) := hB.saved
  have sv1 := sv (48, s.m.core.read .rbx) (by simp [sv6])
  have sv2 := sv (40, s.m.core.read .r12) (by simp [sv6])
  have sv3 := sv (32, s.m.core.read .r13) (by simp [sv6])
  have sv4 := sv (24, s.m.core.read .r14) (by simp [sv6])
  have sv5 := sv (16, s.m.core.read .r15) (by simp [sv6])
  have sv7 := sv (8, s.m.core.read .rbp) (by simp [sv6])
  simp only at sv1 sv2 sv3 sv4 sv5 sv7
  have hret : u.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [Silmaril.X86.FnContract.retOf s.m.core s.m.memory]) := by
    rw [hB.keepX.readBytes (fun j hj => ⟨Or.inr (by omega), fun hx => by have := hX _ hx; omega⟩)]
    exact habi.returnAddress
  have q1 : ((u.m.core.read .rsp).toNat + 168) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 48 := by
    rw [hur]; omega
  have q2 : ((u.m.core.read .rsp).toNat + 176) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 40 := by
    rw [hur]; omega
  have q3 : ((u.m.core.read .rsp).toNat + 184) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 32 := by
    rw [hur]; omega
  have q4 : ((u.m.core.read .rsp).toNat + 192) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 24 := by
    rw [hur]; omega
  have q5 : ((u.m.core.read .rsp).toNat + 200) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 16 := by
    rw [hur]; omega
  have q6 : ((u.m.core.read .rsp).toNat + 208) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 8 := by
    rw [hur]; omega
  have q7 : ((u.m.core.read .rsp).toNat + 216) % 18446744073709551616 = (s.m.core.read .rsp).toNat := by
    rw [hur]; omega
  refine must_listed (o := 320) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q1, sv1]
  refine must_listed (o := 321) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q2, sv2]
  refine must_listed (o := 323) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q3, sv3]
  refine must_listed (o := 325) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q4, sv4]
  refine must_listed (o := 327) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q5, sv5]
  refine must_listed (o := 329) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q6, sv7]
  refine must_listed (o := 330) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q7, hret]
  refine k _ ⟨rfl, ?_, ?_⟩ rfl (by simp [low32]) rfl (by simp [hB.fs])
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_same]; rw [hB.rsp]; bv_omega
  · intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end Silmaril.Elf.Link.Dyn.Sha256sum
