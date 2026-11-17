module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Start

/-! # GNU `sha256sum`: the finalisers `__do_global_dtors_aux` and `_fini`

gcc's crt code, as in hello-gcc (`Hello.GccFini`), at `sha256sum`'s addresses, over any world
whose image is `sha256sum`'s.
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
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- (Any world with `sha256sum`'s image.) **`__do_global_dtors_aux`** (`0x3ae0`): `completed.0`
(`0xa040`) is 0 and `__cxa_finalize` is bound (non-null), so it calls
`__cxa_finalize (__dso_handle)`, then `deregister_tm_clones` (which returns at once), sets
`completed.0` and returns to the gate. -/
theorem sha_dtorsW {b lb : Word} {W : World} (hW : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hcxa : W.fns.find? (·.1 == lb + 0x472c0#64) = some (lb + 0x472c0#64, .cxaFinalize))
    (hcxo : ¬ ShaImg b (lb + 0x472c0#64).toNat) (hgc : W.gate ≠ lb + 0x472c0#64)
    (hcz : lb + 0x472c0#64 ≠ 0#64) {Q : PState → Prop}
    {t : PState} (hc : SCb W b lb t (b + 0x3ae0#64))
    (hbv : loadN t.m.memory (b + 0xa040#64) 1 = some 0#64)
    (hbw : t.m.memory.Permitted .write (b + 0xa040#64).toNat 1)
    (hat : t.g.atexit = [])
    (k : ∀ u : PState, u.m.core.rip = W.gate → u.g = t.g →
      Keeps (fun x => ShaImg b x ∧ x ≠ (b + 0xa040#64).toNat) t.m.memory u.m.memory → MustQ W Q u) :
    MustQ W Q t := by
  have hl := hc.mem.crt
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => by rw [hW]; exact sha_in hb hn
  have hd := hc.done
  have hroom := hc.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have e8 : (t.m.core.read .rsp - 8#64).toNat = (t.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (t.m.core.read .rsp - 8#64 - 8#64).toNat = (t.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  -- push rbp
  have p1 : t.m.memory.Permitted .write (t.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have q1 : t.m.memory.Permitted .read (t.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inl rfl) (by omega) (by omega)
  have hk1 : Keeps (ShaImg b) t.m.memory
      (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rbp)) :=
    skeeps_push hW hroom (by omega) (by omega)
  have hm1 := hc.mem.keep hb hk1
  -- call __cxa_finalize@plt
  have p2 : (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rbp)).Permitted .write
      (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inr rfl) (by omega) (by omega)
  have q2 : (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rbp)).Permitted .read
      (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inl rfl) (by omega) (by omega)
  have hk2 : Keeps (ShaImg b) t.m.memory (pushMem (pushMem t.m.memory (t.m.core.read .rsp)
      (t.m.core.read .rbp)) (t.m.core.read .rsp - 8#64) (b + 0x3b07#64)) :=
    hk1.trans (skeeps_push hW hroom.pushMem (by omega) (by omega))
  have hm2 := hc.mem.keep hb hk2
  have hret2 := pushMem_read (v := b + 0x3b07#64) q2 p2
  have hz1 : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN (BitVec.setWidth 8 (0#64)) 0#8)
      Silmaril.X86.Ext.Cond.ne = some false := by decide
  have hz2 : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp
      (lb + 0x472c0#64) 0#64) Silmaril.X86.Ext.Cond.e = some false := by
    show Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN _ _) _ = _
    rw [eval_e_sub]; simpa using hcz
  refine must_listed (o := 160) sha_listing_ok.2.1 rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip, ripadd]) ?_
  xstep [hc.rip]
  refine must_listed (o := 164) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [hbv, Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits]
  refine must_listed (o := 171) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [hz1]
  refine must_listed (o := 173) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  refine must_listed (o := 174) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hm1.crt (by rw [ripadd]) ?_
  xstep [hm1.cxa]
  refine must_listed (o := 182) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hm1.crt (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 185) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hm1.crt (by rw [ripadd]) ?_
  xstep [hz2]
  refine must_listed (o := 187) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hm1.crt (by rw [ripadd]) ?_
  xstep [hm1.dso]
  refine must_listed (o := 194) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hm1.crt (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p2)]
  xstep []
  refine must_listed (o := 0) sha_listing_ok.2.2.2 rfl hd (hin _ (by decide)) hm2.pltgot (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 4) sha_listing_ok.2.2.2 rfl hd (hin _ (by decide)) hm2.pltgot (by rw [ripadd]) ?_
  xstep [hm2.cxa]
  have hsp' : (t.m.core.read .rsp - 8#64 - 8#64).toNat % 16 = 8 := by rw [e16]; have := hc.al; omega
  refine must_fn hd (by rw [hW]; exact hcxo) (by simpa using (Ne.symm hgc))
    hlz (f := .cxaFinalize) (by simpa using hcxa) (fun r => Iff.rfl)
    ⟨abiEntry_of (v := b + 0x3b07#64) (by simpa using hsp') (by simpa using hret2), by simpa using hat⟩ ?_
  rintro u ⟨⟨habi, hkeep⟩, hg, -⟩
  simp only at habi hkeep hg
  -- the memories: m2 (before `__cxa_finalize`), u, m3 (after `call deregister_tm_clones`)
  have hrsp_c : (t.m.core.read .rsp - 8#64 - 8#64).toNat = (t.m.core.read .rsp).toNat - 16 := e16
  have hrip_u : u.m.core.rip = b + 0x3b07#64 := by
    rw [habi.pc]; exact retOf_of (by simpa using hret2)
  have hrsp_u : u.m.core.read .rsp = t.m.core.read .rsp - 8#64 := by
    rw [habi.stack]; simp
  have hkU : Keeps (fun a => W.Kept a ∨
      (t.m.core.read .rsp - 8#64 - 8#64).toNat ≤ a)
      (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rbp))
        (t.m.core.read .rsp - 8#64) (b + 0x3b07#64)) u.m.memory := by simpa using hkeep
  have hkUi : Keeps (ShaImg b) t.m.memory u.m.memory :=
    hk2.trans (hkU.mono (fun a ha => Or.inl (Or.inl (by rw [hW]; exact ha))))
  have hmu := hc.mem.keep hb hkUi
  -- permissions on the stack and on `completed.0` in `u`
  have pU : ∀ acc, acc = Access.read ∨ acc = Access.write →
      u.m.memory.Permitted acc (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 := by
    intro acc hacc
    rw [hkU.permitted (fun k hk => Or.inr (by omega))]
    exact perm_room hroom.pushMem.pushMem hacc (by omega) (by omega)
  have hk3 : Keeps (ShaImg b) u.m.memory (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x3b0c#64)) := by
    apply pushMem_keeps
    intro x hx
    have := (hroom.2.2 x)
    by_contra hc'
    have h' := this (by rw [e16] at hc'; omega) (by rw [e16] at hc'; omega)
    exact h'.2.2 (Or.inl (by rw [hW]; exact hx))
  have hm3 := hmu.keep hb hk3
  have hret3 := pushMem_read (m := u.m.memory) (sp := t.m.core.read .rsp - 8#64) (v := b + 0x3b0c#64)
    (pU _ (Or.inl rfl)) (pU _ (Or.inr rfl))
  have hz3 : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp
      (b + 41016#64) (b + 41016#64)) Silmaril.X86.Ext.Cond.e = some true := by
    show Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN _ _) _ = _
    rw [eval_e_sub]; simp
  have hwb : (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x3b0c#64)).Permitted .write
      (b + 0xa040#64).toNat 1 := by
    rw [pushMem_permitted]
    rw [hkU.permitted (fun k hk => Or.inl (Or.inl <| by
      have := sha_in hb (n := 0xa040) (by decide)
      rw [addr_toNat (by have := hb; omega)] at this ⊢
      rw [hW]; simp only [ShaImg] at this ⊢; omega))]
    rw [pushMem_permitted, pushMem_permitted]
    exact hbw
  have hdu : u.g.done = none := by rw [hg]; exact hd
  refine must_listed (o := 199) sha_listing_ok.2.1 rfl hdu (by rw [hrip_u]; exact hin _ (by decide))
    hmu.crt (by rw [hrip_u, ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [hrsp_u] using pU _ (Or.inr rfl))]
  xstep [hrip_u, hrsp_u]
  refine must_listed (o := 48) sha_listing_ok.2.1 rfl hdu (hin _ (by decide)) hm3.crt (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 55) sha_listing_ok.2.1 rfl hdu (hin _ (by decide)) hm3.crt (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 62) sha_listing_ok.2.1 rfl hdu (hin _ (by decide)) hm3.crt (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 65) sha_listing_ok.2.1 rfl hdu (hin _ (by decide)) hm3.crt (by rw [ripadd]) ?_
  xstep [hz3]
  refine must_listed (o := 88) sha_listing_ok.2.1 rfl hdu (hin _ (by decide)) hm3.crt (by rw [ripadd]) ?_
  have hA : (18446744073709551608 + (18446744073709551608 + (t.m.core.read .rsp).toNat)) %
      18446744073709551616 = (t.m.core.read .rsp - 8#64 - 8#64).toNat := by rw [e16]; omega
  xstep [Silmaril.X86.popWord]
  rw [hA, hret3]
  simp only [obind_some, Silmaril.X86.wordOfBytes?_encodeWords, WP_ok, st_write_regs]
  refine must_listed (o := 204) sha_listing_ok.2.1 rfl hdu (hin _ (by decide)) hm3.crt (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.writeRM8]
  rw [storeN_ok hwb]
  xstep []
  -- the stack below `completed.0`'s store: the saved `rbp` and the gate
  have hstk : ∀ x, (t.m.core.read .rsp).toNat - 16 ≤ x → x < (t.m.core.read .rsp).toNat + 8 →
      ¬ ShaImg b x := fun x h1 h2 => by
    have := (hroom.2.2 x (by omega) h2).2.2
    exact fun h => this (Or.inl (by rw [hW]; exact h))
  have hbssA : (b + 0xa040#64).toNat = b.toNat + 0xa040 := addr_toNat (by have := hb; omega)
  have hbssI : ShaImg b (b.toNat + 0xa040) := ⟨by omega, by have := hb; omega⟩
  have hk4 : Keeps (fun x => (t.m.core.read .rsp).toNat - 16 ≤ x ∧ x < (t.m.core.read .rsp).toNat + 8)
      (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x3b0c#64))
      (storeMem (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x3b0c#64)) (b + 41024#64) 1
        1#64) := by
    apply storeMem_keeps
    intro x ⟨h1, h2⟩
    have := hstk x h1 h2
    rw [show (b + 41024#64) = b + 0xa040#64 from rfl, hbssA]
    by_contra hc'
    exact this (by rw [show x = b.toNat + 0xa040 by omega]; exact hbssI)
  have hRbp : (storeMem (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x3b0c#64)) (b + 41024#64) 1
        1#64).readBytes (t.m.core.read .rsp - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [t.m.core.read .rbp]) := by
    rw [hk4.readBytes (fun k hk => ⟨by omega, by omega⟩)]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat - 8 ≤ x)
      (fun x hx => Or.inr (by rw [e16]; omega))).readBytes (fun k hk => by omega)]
    rw [hkU.readBytes (fun k hk => Or.inr (by omega))]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat - 8 ≤ x)
      (fun x hx => Or.inr (by rw [e16]; omega))).readBytes (fun k hk => by omega)]
    exact pushMem_read q1 p1
  have hRgate : (storeMem (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x3b0c#64)) (b + 41024#64) 1
        1#64).readBytes (t.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [W.gate]) := by
    rw [hk4.readBytes (fun k hk => ⟨by omega, by omega⟩)]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x)
      (fun x hx => Or.inr (by rw [e16]; omega))).readBytes (fun k hk => by omega)]
    rw [hkU.readBytes (fun k hk => Or.inr (by omega))]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x)
      (fun x hx => Or.inr (by rw [e16]; omega))).readBytes (fun k hk => by omega)]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x)
      (fun x hx => Or.inr (by rw [e8]; omega))).readBytes (fun k hk => by omega)]
    exact hc.ret
  have hK4 : Keeps (fun x => ShaImg b x ∧ x ≠ (b + 0xa040#64).toNat) t.m.memory
      (storeMem (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x3b0c#64)) (b + 41024#64) 1 1#64) :=
    ((hkUi.trans hk3).mono fun x hx => hx.1).trans (storeMem_keeps fun x hx => by
      rw [show (b + 41024#64) = b + 0xa040#64 from rfl, hbssA]
      rw [hbssA] at hx
      omega)
  have hl4 : Loaded (storeMem (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x3b0c#64))
      (b + 41024#64) 1 1#64) (b + 0x3a40#64) shaCrtText := by
    have e : (b + 0x3a40#64).toNat = b.toNat + 0x3a40 := addr_toNat (by omega)
    have hl0 := hc.mem.crt
    unfold Loaded Memory.fetchBytes at hl0 ⊢
    rw [hK4.readWith (fun j hj => by
      rw [e, hbssA]; rw [sha_lens.2.1] at hj; exact ⟨⟨by omega, by omega⟩, by omega⟩)]
    exact hl0
  have hB : (18446744073709551608 + (t.m.core.read .rsp).toNat) % 18446744073709551616 =
      (t.m.core.read .rsp - 8#64).toNat := by rw [e8]; omega
  refine must_listed (o := 211) sha_listing_ok.2.1 rfl hdu (hin _ (by decide)) hl4 (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord]
  rw [hB, hRbp]
  simp only [obind_some, Silmaril.X86.wordOfBytes?_encodeWords, WP_ok, st_write_regs]
  refine must_listed (o := 212) sha_listing_ok.2.1 rfl hdu (hin _ (by decide)) hl4 (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hRgate]
  exact k _ rfl hg hK4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- (Any world with `sha256sum`'s image.) **`_fini`** (`0x6d44`). -/
theorem sha_finiW {b : Word} {W : World} (hW : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) {Q : PState → Prop} {t : PState}
    (hrip : t.m.core.rip = b + 0x6d44#64) (hd : t.g.done = none)
    (hl : Loaded t.m.memory (b + 0x6d44#64) shaFiniText)
    (hret : t.m.memory.readBytes (t.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [W.gate]))
    (k : ∀ u : PState, u.m.core.rip = W.gate → u.g = t.g → u.m.memory = t.m.memory → MustQ W Q u) :
    MustQ W Q t := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => by rw [hW]; exact sha_in hb hn
  refine must_listed (o := 0) sha_listing_ok.2.2.1 rfl hd (by rw [hrip]; exact hin _ (by decide)) hl
    (by rw [hrip]; exact (BitVec.add_zero _).symm) ?_
  xstep [hrip]
  refine must_listed (o := 4) sha_listing_ok.2.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 8) sha_listing_ok.2.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 12) sha_listing_ok.2.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hret]
  exact k _ rfl rfl rfl

end Silmaril.Elf.Link.Dyn.Sha256sum
