module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainLocale

/-! # GNU `sha256sum`: `main` from `atexit (close_stdout)` to the end of option parsing

`0x2820`–`0x29fd`: `atexit (close_stdout)` (gnulib's `atexit` at `0x6d30` tail-calls
`__cxa_atexit (close_stdout, NULL, __dso_handle)`), `setvbuf (stdout, NULL, _IOLBF, 0)`, the
option flags in the frame, and `getopt_long`, which on an argument vector without options
returns `-1` at once.

`cxaAtexitFirst`: the contract of `__cxa_atexit` used here: with fewer than 32 handlers
registered it registers `f` and returns 0 (glibc keeps the first 32 handlers in a static
list, so these registrations cannot fail).
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

/-- **`__cxa_atexit (f, arg, d)`** while fewer than 32 handlers are registered. -/
def cxaAtexitFirst (W : World) (s : PState) : Silmaril.X86.RelIsa.Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ s.g.atexit.length < 32)
    fun t => Returns W s t ∧ low32 (t.m.core.read .rax) = 0 ∧
      t.g = { s.g with atexit := s.g.atexit ++ [s.m.core.read .rdi] }

/-- `mov byte [base + d], imm8`. -/
theorem exec_storeb_d (base : Reg) (d : BitVec 32) (imm : BitVec 8) (c : State) (m : Memory) (l : Nat)
    (h : m.Permitted .write (c.read base + d.signExtend 64).toNat 1) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.movI8 (.mem (Silmaril.X86.Ext.Mem.ofReg base Option.none d)) imm)))
      c m l = .ok { c with rip := c.rip + BitVec.ofNat 64 l }
        (storeMem m (c.read base + d.signExtend 64) 1 (imm.setWidth 64)) := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM8, storeN_ok h, ofReg_addr]

/-- `mov dword [base + d], imm32`. -/
theorem exec_storeI32_d (base : Reg) (d imm : BitVec 32) (c : State) (m : Memory) (l : Nat)
    (h : m.Permitted .write (c.read base + d.signExtend 64).toNat 4) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.movI .d (.mem (Silmaril.X86.Ext.Mem.ofReg base Option.none d)) imm)))
      c m l = .ok { c with rip := c.rip + BitVec.ofNat 64 l }
        (storeMem m (c.read base + d.signExtend 64) 4 ((imm.signExtend 32).setWidth 64)) := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM, storeN_ok h, ofReg_addr, Silmaril.X86.Ext.Sz.bytes]

/-- A return relation from a state with the same stack, memory and callee-saved registers. -/
theorem returnsExcept_congr {W : World} {fp : Nat → Prop} {j e t : PState} (hm : j.m.memory = e.m.memory)
    (hsp : j.m.core.read .rsp = e.m.core.read .rsp)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, j.m.core.read r = e.m.core.read r)
    (h : ReturnsExcept W fp j t) : ReturnsExcept W fp e t := by
  obtain ⟨⟨hpc, hst, hc⟩, hk⟩ := h
  have hret : Silmaril.X86.FnContract.retOf j.m.core j.m.memory = Silmaril.X86.FnContract.retOf e.m.core e.m.memory := by
    simp only [Silmaril.X86.FnContract.retOf, hm, hsp]
  refine ⟨⟨by rw [hpc, hret], by rw [hst, hsp], fun r hr => by rw [hc r hr, hcs r hr]⟩, ?_⟩
  rw [← hm, ← hsp]; exact hk

/-- The library frame from a state with the same stack, memory, `fsBase` and callee-saved registers. -/
theorem libRet_congr {E : Env} {W : World} {fp : Nat → Prop} {j e t : PState} (hm : j.m.memory = e.m.memory)
    (hsp : j.m.core.read .rsp = e.m.core.read .rsp) (hfs : j.m.core.fsBase = e.m.core.fsBase)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, j.m.core.read r = e.m.core.read r)
    (h : LibRet E W fp j t) : LibRet E W fp e t := by
  obtain ⟨hr, hf, hst, hk, hp, hpm, hnm, hnn⟩ := h
  refine ⟨returnsExcept_congr hm hsp hcs hr, hf.trans hfs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a h1 h2 acc; rw [← hm]; exact hst a (by rw [hsp]; exact h1) (by rw [hsp]; exact h2) acc
  · rw [← hm]; exact hk
  · rw [← hm]; exact hp
  · rw [← hm]; exact hpm
  · unfold NoMap at hnm ⊢; rw [← hm]; exact hnm
  · unfold NoNewStream at hnn ⊢; rw [← hm]; exact hnn

theorem othersKept_congr {E : Env} {j e t : PState} {fs : List Word} (hm : j.m.memory = e.m.memory)
    (h : OthersKept E j t fs) : OthersKept E e t fs := by
  intro f st hf h'; rw [← hm] at h'; exact h f st hf h'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`atexit (close_stdout)`** (`0x2820`–`0x282c`): `close_stdout` (`0x69b0`) is registered. -/
theorem sha_main_atexit {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hA : ImpOk W (lb + 0x471f0#64) (nm "__cxa_atexit") (framed E W (fun _ _ => False) (cxaAtexitFirst W)))
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s s1 x : PState} {g : Word}
    (hL : MainLoc E W b lb kb sr sc C fi sto ste sti s s1 x g) (hat : x.g.atexit = [])
    (hal : (s.m.core.read .rsp).toNat % 16 = 8) (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (k : ∀ y, Body W (ShaMemAll b lb kb sr sc) s1 y 328 4096 (sv6 s1) → y.m.core.rip = b + 0x282c#64 →
      y.m.core.read .rsp = x.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, y.m.core.read r = x.m.core.read r) →
      y.g = { x.g with atexit := [b + 0x69b0#64] } → MEnv E W b lb C fi sto ste sti y.m.memory →
      Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat - 328 ≤ a)) x.m.memory y.m.memory →
      Keeps C x.m.memory y.m.memory → MustQ W Q y) : MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I hb hn
  have hB := hL.body
  have hsp1 : s1.m.core.read .rsp = s.m.core.read .rsp := by rw [hL.base]
  have hroom : Room W x.m.memory (s.m.core.read .rsp) 4096 := hsp1 ▸ hB.room
  have hsp := hroom.1
  have hd := hB.done
  have hMk := shaMemAll_keepI (lb := lb) (kb := kb) (sr := sr) (sc := sc) I hb
  have hxsp : (x.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 328 := by
    rw [hB.rsp, hsp1]; exact sub_toNat (by omega) (by omega)
  have hx8 : (x.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 336 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hxsp]; omega
  have hpw : x.m.memory.Permitted .write (x.m.core.read .rsp - 8#64).toNat 8 := by
    rw [hx8]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have hpr : x.m.memory.Permitted .read (x.m.core.read .rsp - 8#64).toNat 8 := by
    rw [hx8]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  refine must_listed (o := 208) shaM_listing_ok.1 rfl hd (by rw [hL.rip]; exact hin _ (by decide))
    hB.mem.mn.mainA (by rw [hL.rip, ripadd]) ?_
  xstep [hL.rip]
  refine must_gen (fun u => u.m.core.rip = b + 0x2827#64 ∧ u.m.memory = x.m.memory ∧ u.g = x.g ∧
      u.m.core.read .rdi = b + 0x69b0#64 ∧ u.m.core.fsBase = x.m.core.fsBase ∧
      (∀ r, r ≠ .rdi → u.m.core.read r = x.m.core.read r)) ?_ ?_
  · exact ⟨by simp, rfl, rfl, by simp, rfl, fun r h => by simp [h]⟩
  rintro u ⟨hru, hmu, hgu, hdiu, hfsu, hregu⟩
  have hspu : u.m.core.read .rsp = x.m.core.read .rsp := hregu _ (by decide)
  have hdu : u.g.done = none := by rw [hgu]; exact hd
  refine must_listed (o := 215) shaM_listing_ok.1 rfl hdu (by rw [hru]; exact hin _ (by decide))
    (by rw [hmu]; exact hB.mem.mn.mainA) (by rw [hru, ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by rw [hspu, hmu]; exact hpw)]
  xstep [hru]
  have hmE : ShaMemAll b lb kb sr sc (pushMem u.m.memory (u.m.core.read .rsp) (b + 0x282c#64)) := by
    rw [hmu]
    exact hMk _ _ hB.mem (room_push_img hroom (by rw [hspu]; omega) (by rw [hspu]; omega))
  refine must_gen (fun e => e.m.core.rip = b + 0x6d30#64 ∧
      e.m.memory = pushMem u.m.memory (u.m.core.read .rsp) (b + 0x282c#64) ∧ e.g = x.g ∧
      e.m.core.read .rsp = u.m.core.read .rsp - 8#64 ∧ e.m.core.fsBase = x.m.core.fsBase ∧
      (∀ r, r ≠ .rsp → e.m.core.read r = u.m.core.read r)) ?_ ?_
  · refine ⟨?_, ?_, hgu, by simp, by simp [hfsu], fun r h => by simp [h]⟩
    · rfl
    · rfl
  rintro e ⟨hre, hme, hge, hspe, hfse, hrege⟩
  have hmE' : ShaMemAll b lb kb sr sc e.m.memory := by rw [hme]; exact hmE
  have hde : e.g.done = none := by rw [hge]; exact hd
  have hspux : u.m.core.read .rsp = x.m.core.read .rsp := hspu
  have hret : e.m.memory.readBytes (e.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 0x282c#64]) := by
    rw [hme, hspe]; exact pushMem_read (by rw [hspux, hmu]; exact hpr) (by rw [hspux, hmu]; exact hpw)
  have hcse : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, e.m.core.read r = x.m.core.read r := by
    intro r hr
    have h1 : r ≠ .rsp := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    have h2 : r ≠ .rdi := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    rw [hrege r h1, hregu r h2]
  refine must_listed (o := 0) shaM_listing_ok.2.2.2.2 rfl hde (by rw [hre]; exact hin _ (by decide))
    hmE'.mn.atexit (by rw [hre]; exact (BitVec.add_zero _).symm) ?_
  xstep [hre]
  refine must_listed (o := 4) shaM_listing_ok.2.2.2.2 rfl hde (hin _ (by decide)) hmE'.mn.atexit
    (by rw [ripadd]) ?_
  xstep [hmE'.st.dso]
  refine must_listed (o := 11) shaM_listing_ok.2.2.2.2 rfl hde (hin _ (by decide)) hmE'.mn.atexit
    (by simp only [ripadd]) ?_
  xstep []
  refine must_plt_jmp (o := 13) (so := 0x130) (pb := b + 0x23c0#64) hde hlz shaM_listing_ok.2.2.2.2 rfl
    (hin _ (by decide)) hmE'.mn.atexit (by simp only [ripadd]) shaC_listing_ok.1 rfl rfl
    (by simp only [BitVec.add_assoc]; rfl) (img_off I hb (by decide)) (img_off I hb (by decide)) hmE'.cl.plt
    (by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x130 + 4 + 6) + BitVec.signExtend 64 0x7976#32 = b + 0x9e70#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact hmE'.mn.cxaAtexit)
    hA.1 hA.2.1 hA.2.2.1
    (pre := e.g.atexit.length < 32)
    (post := fun t => LibRet E W (fun _ => False) e t ∧ OthersKept E e t [] ∧
      t.g = { e.g with atexit := e.g.atexit ++ [b + 0x69b0#64] })
    (fun r h hp => by
      have hal8 : (e.m.core.read .rsp).toNat % 16 = 8 := by rw [hspe, hspux]; omega
      obtain ⟨t, ht, hq⟩ := ((impOk_fn hA _ r).1 h).1
        ⟨abiEntry_of (v := b + 0x282c#64) (by simpa [jmpEntry] using hal8) (by simpa [jmpEntry] using hret),
          by simpa [jmpEntry] using hp⟩
      obtain ⟨hl, ho⟩ := ((impOk_fn hA _ r).1 h).2.1 (fun _ h => h.elim) t ht
      simp only at hl
      refine ⟨t, ht, libRet_congr (h := hl) (hm := by exact rfl) (hsp := by exact rfl) (hfs := by exact rfl) (hcs := fun r hr => ?_),
        othersKept_congr (by exact rfl) ho, ?_⟩
      · have h1 : r ≠ .rdx := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
        have h2 : r ≠ .rsi := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
        simp only [jmpEntry, st_read_mk, Silmaril.Machine.RegisterFile.write_other _ _ _ _ h1,
          Silmaril.Machine.RegisterFile.write_other _ _ _ _ h2, st_regs_apply]
      · rw [hq.2.2]; simp [jmpEntry, hrege _ (by decide : Reg.rdi ≠ .rsp), hdiu])
    (by rw [hge, hat]; decide) ?_
  rintro t ⟨hlt, hot, hgt⟩
  have hem : e.m.memory = pushMem x.m.memory (x.m.core.read .rsp) (b + 0x282c#64) := by rw [hme, hmu, hspux]
  have hesp : e.m.core.read .rsp = x.m.core.read .rsp - 8#64 := by rw [hspe, hspux]
  have hsv : ∀ p ∈ sv6 s1, p.1 ≤ 48 ∧ 48 ≤ 328 := sv6_bound328 s1
  obtain ⟨hBt, hrt, hspt, hcst⟩ := body_after hMk hB (by decide) (by decide) hsv hem hesp hcse
    (by rw [hfse]) (fp := fun _ => False)
    ⟨hlt.1, halfOfStack hlt.2.2.1, by rw [hgt, hge]; exact hd⟩ hlt.2.1 (fun x h => h.elim) (fun x h => h.elim)
  have henvE : MEnv E W b lb C fi sto ste sti e.m.memory := by
    rw [hem]
    refine hL.env.push (by rw [hx8]; omega) fun a h1 h2 => ?_
    rw [hx8] at h1 h2
    exact ⟨(hroom.2.2 a (by omega) (by omega)).2.2, fun hc => by have := hC a hc; omega⟩
  refine k t hBt hrt hspt hcst ?_ (MEnv.lib I henvE hlt hot (fun a h => h.elim)) ?_ ?_
  · rw [hgt, hge, hat]; rfl
  rotate_left
  · have hp1 : Keeps C x.m.memory e.m.memory := by
      rw [hem]; exact pushMem_keeps fun a ha => by rw [hx8]; have := hC a ha; omega
    exact hp1.trans (hlt.2.2.2.1.mono fun a ha =>
      ⟨(henvE.np a (Or.inr ha)).1, fun h => h, (henvE.np a (Or.inr ha)).2⟩)
  · have hk := hlt.1.2
    rw [hem, hesp, hx8] at hk
    refine (pushMem_keeps fun a ha => ?_).trans (hk.mono fun a ha => ⟨?_, fun h => h⟩)
    · rw [hx8]
      rcases ha with ha | ha
      · by_contra hc; exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
      · omega
    · rcases ha with ha | ha
      · exact Or.inl ha
      · right; omega

/-- What holds in `main`'s body at `ip`, with base `s1` (registers of `main`'s entry `s`). -/
structure MainAt (E : Env) (W : World) (b lb kb sr sc : Word) (C : Nat → Prop) (fi : Word)
    (sto ste sti : St) (s s1 x : PState) (g ip : Word) (G : Ghost) : Prop where
  body : Body W (ShaMemAll b lb kb sr sc) s1 x 328 4096 (sv6 s1)
  base : s1.m.core = s.m.core
  bg : s1.g = s.g
  ret : s1.m.memory.readBytes (s.m.core.read .rsp).toNat 8 = s.m.memory.readBytes (s.m.core.read .rsp).toNat 8
  kargs : Keeps W.args s.m.memory s1.m.memory
  rip : x.m.core.rip = ip
  rbp : x.m.core.read .rbp = s.m.core.read .rsp - 8#64
  r12 : BitVec.setWidth 32 (x.m.core.read .r12) = BitVec.setWidth 32 (s.m.core.read .rdi)
  rbx : x.m.core.read .rbx = s.m.core.read .rsi
  r14 : x.m.core.read .r14 = b + 0x71af#64
  r15 : x.m.core.read .r15 = b + 0x9a20#64
  guard : x.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  g : x.g = G
  env : MEnv E W b lb C fi sto ste sti x.m.memory
  rw : ShaRw b x.m.memory
  /-- the image below the option variables, and the kept memory outside the image, are as at
  `main`'s entry (bytes and permissions) -/
  kimg : Keeps (fun a => ImgW b a ∨ (W.Kept a ∧ ¬ ShaImg b a)) s.m.memory s1.m.memory
  /-- `have_read_stdin` (`.bss` `0xa160`, not written by the head) is as at `main`'s entry -/
  khr : s1.m.memory.readBytes (b.toNat + 0xa160) 1 = s.m.memory.readBytes (b.toNat + 0xa160) 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`atexit (close_stdout)` and `setvbuf (stdout, NULL, _IOLBF, 0)`** (`0x2820`–`0x2844`), keeping
`program_invocation_name` (K8). -/
theorem sha_main_bufP {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hA : ImpOk W (lb + 0x471f0#64) (nm "__cxa_atexit") (framed E W (fun _ _ => False) (cxaAtexitFirst W)))
    (hV : ImpOk W (lb + 0x88630#64) (nm "setvbuf") (setvbufStep E W))
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s s1 x : PState} {g : Word}
    (hL : MainLoc E W b lb kb sr sc C fi sto ste sti s s1 x g) (hat : x.g.atexit = [])
    (hal : (s.m.core.read .rsp).toNat % 16 = 8) (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (k : ∀ y, MainAt E W b lb kb sr sc C fi sto ste sti s s1 y g (b + 0x2844#64)
      { s.g with atexit := [b + 0x69b0#64] } → Keeps C x.m.memory y.m.memory → MustQ W Q y) : MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I hb hn
  have hsp1 : s1.m.core.read .rsp = s.m.core.read .rsp := by rw [hL.base]
  refine sha_main_atexit I hb hlz hA hL hat hal hlo hC ?_
  intro y hBy hry hspy hcsy hgy henvy hky hkcy
  have hdy : y.g.done = none := hBy.done
  have hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, y.m.core.read r = x.m.core.read r := hcsy
  refine must_listed (o := 220) shaM_listing_ok.1 rfl hdy (by rw [hry]; exact hin _ (by decide))
    hBy.mem.mn.mainA (by rw [hry, ripadd]) ?_
  xstep [hry, hBy.mem.cl.stdoutV]
  refine must_listed (o := 227) shaM_listing_ok.1 rfl hdy (hin _ (by decide)) hBy.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep []
  refine must_listed (o := 229) shaM_listing_ok.1 rfl hdy (hin _ (by decide)) hBy.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep []
  refine must_listed (o := 231) shaM_listing_ok.1 rfl hdy (hin _ (by decide)) hBy.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep []
  refine must_gen (fun u => u.m.core.rip = b + 0x283c#64 ∧ u.m.memory = y.m.memory ∧ u.g = y.g ∧
      u.m.core.read .rax = lb + 0x2056a8#64 ∧ u.m.core.fsBase = y.m.core.fsBase ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, u.m.core.read r = y.m.core.read r) ∧
      u.m.core.read .rsp = y.m.core.read .rsp) ?_ ?_
  · refine ⟨by simp, rfl, rfl, by simp, rfl, fun r hr => ?_, by simp⟩
    have h1 : r ≠ .rax := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    have h2 : r ≠ .rcx := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    have h3 : r ≠ .rsi := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    have h4 : r ≠ .rdx := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    simp [h1, h2, h3, h4]
  rintro u ⟨hru, hmu, hgu, haxu, hfsu, hcsu, hspu⟩
  have hdu : u.g.done = none := by rw [hgu]; exact hdy
  have hout : loadN u.m.memory (u.m.core.read .rax + BitVec.signExtend 64 0#32) 8 = some E.stdoutF := by
    rw [haxu, hmu, show BitVec.signExtend 64 0#32 = 0#64 by decide, BitVec.add_zero]; exact henvy.vars.out
  refine must_listed (o := 236) shaM_listing_ok.1 rfl hdu (by rw [hru]; exact hin _ (by decide))
    (by rw [hmu]; exact hBy.mem.mn.mainA) (by rw [hru, ripadd]) ?_
  rw [exec_loadqd _ _ _ _ _ _ _ hout, WP_ok]
  have hBu : Body W (ShaMemAll b lb kb sr sc) s1 u 328 4096 (sv6 s1) :=
    hBy.of_eq hmu hspu hfsu (by rw [hgu])
  refine main_callC I hb hlz (s := s1) (hBu.of_eq rfl (by simp) rfl rfl) (by rw [hsp1]; exact hal)
    (by rw [hsp1]; exact hlo) (by rw [hsp1]; exact hC) (by rw [hmu]; exact henvy)
    shaM_listing_ok.1 (fun m h => h.mn.mainA) (o := 239) rfl (by rw [hru, ripadd]; exact hin _ (by decide))
    (by simp only [hru, ripadd])
    (so := 0x10) rfl rfl (by simp only [BitVec.add_assoc]; rfl) (by decide) hV
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x10 + 4 + 6) + BitVec.signExtend 64 0x7a06#32 = b + 0x9de0#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.mn.setvbuf)
    (R := fun _ => True) (fp := fun _ => False)
    (fun r h hp => by
      obtain ⟨t, ht, hl, hg', ho⟩ := h hp
      exact ⟨t, ht, hl, ho, hg', trivial⟩)
    (fun he _ => he) (fun x h => h.elim) ?_
  intro z _ hBz hrz hspz hcsz hgz henvz hkz hkcz
  have hpinz : Keeps C x.m.memory z.m.memory := hkcy.trans (by rw [← hmu]; exact hkcz)
  have hcsz' : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, z.m.core.read r = x.m.core.read r := by
    intro r hr
    have h1 : r ≠ .rdi := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    rw [hcsz r hr]
    have : (u.m.core.write .rdi E.stdoutF).read r = u.m.core.read r :=
      Silmaril.X86.State.read_write_other _ _ _ _ h1
    simp only [st_read_mk, st_regs_apply] at this ⊢
    rw [this, hcsu r hr, hcs r hr]
  have hcR : ∀ r, r ∈ Silmaril.X86.sysv64.calleeSaved → z.m.core.read r = x.m.core.read r := hcsz'
  refine k z ⟨hBz, hL.base, hL.bg, hL.ret, hL.kargs, by rw [hrz, BitVec.add_assoc]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, henvz, ?_,
    hL.kimg, hL.khr⟩ hpinz
  · rw [hcR .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hL.rbp
  · rw [hcR .r12 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hL.r12
  · rw [hcR .rbx (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hL.rbx
  · rw [hcR .r14 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hL.r14
  · rw [hcR .r15 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hL.r15
  · rw [hkz.readBytes (fun j hj => ⟨Or.inr (by rw [hsp1]; omega), fun h => h⟩), hmu,
      hky.readBytes (fun j hj => Or.inr (by omega))]
    exact hL.guard
  · rw [hgz, hgu, hgy, hL.g]
  · intro j hj
    have hi : W.Kept (b.toNat + 0xa160 + j) := Or.inl (by rw [I]; exact ⟨by omega, by omega⟩)
    rw [(hkz _ ⟨Or.inl hi, fun h => h⟩).2, (hkz _ ⟨Or.inl hi, fun h => h⟩).2, hmu,
      (hky _ (Or.inl hi)).2, (hky _ (Or.inl hi)).2]
    exact hL.rw j hj

/-- **`atexit (close_stdout)` and `setvbuf (stdout, NULL, _IOLBF, 0)`** (`0x2820`–`0x2844`). -/
theorem sha_main_buf {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hA : ImpOk W (lb + 0x471f0#64) (nm "__cxa_atexit") (framed E W (fun _ _ => False) (cxaAtexitFirst W)))
    (hV : ImpOk W (lb + 0x88630#64) (nm "setvbuf") (setvbufStep E W))
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s s1 x : PState} {g : Word}
    (hL : MainLoc E W b lb kb sr sc C fi sto ste sti s s1 x g) (hat : x.g.atexit = [])
    (hal : (s.m.core.read .rsp).toNat % 16 = 8) (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (k : ∀ y, MainAt E W b lb kb sr sc C fi sto ste sti s s1 y g (b + 0x2844#64)
      { s.g with atexit := [b + 0x69b0#64] } → MustQ W Q y) : MustQ W Q x :=
  sha_main_bufP I hb hlz hA hV hL hat hal hlo hC fun y hy _ => k y hy

end Silmaril.Elf.Link.Dyn.Sha256sum
