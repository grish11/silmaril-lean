module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainCall

/-! # GNU `sha256sum`: `main` from `set_program_name`'s stores through the locale set-up

`0x27cb`–`0x2820`: `program_name = argv[0]` (`.bss` `0xa180`), `program_invocation_name =
argv[0]` (libc), `setlocale (LC_ALL, "")`, `bindtextdomain ("coreutils", "/usr/share/locale")`,
`textdomain ("coreutils")`.
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

theorem permitted_of {m : Memory} {acc : Access} {a len : Nat} (h1 : a + len < 2 ^ 64)
    (h : ∀ k, k < len → m.permits acc (a + k) = true) : m.Permitted acc a len := by
  rw [Memory.Permitted, Memory.checkSpan_iff]
  simp only [Silmaril.Process.addressLimit]
  exact ⟨by omega, by omega, h⟩

/-- The imports of the locale set-up, with their (framed, quiet) contracts. -/
structure LocImps (E : Env) (W : World) (lb : Word) : Prop where
  setlocale : ImpOk W (lb + 0x3a6b0#64) (nm "setlocale") (framed E W (fun _ _ => False) (quietStep W fun _ => True))
  bindtextdomain : ImpOk W (lb + 0x3bf00#64) (nm "bindtextdomain")
    (framed E W (fun _ _ => False) (quietStep W fun _ => True))
  textdomain : ImpOk W (lb + 0x406f0#64) (nm "textdomain") (framed E W (fun _ _ => False) (quietStep W fun _ => True))

/-- What holds at `0x2820` (before `atexit (close_stdout)`), with a new base `s1` (the same
registers as `main`'s entry `s`, the memory after the two stores). -/
structure MainLoc (E : Env) (W : World) (b lb kb sr sc : Word) (C : Nat → Prop) (fi : Word)
    (sto ste sti : St) (s s1 x : PState) (g : Word) : Prop where
  body : Body W (ShaMemAll b lb kb sr sc) s1 x 328 4096 (sv6 s1)
  base : s1.m.core = s.m.core
  bg : s1.g = s.g
  ret : s1.m.memory.readBytes (s.m.core.read .rsp).toNat 8 = s.m.memory.readBytes (s.m.core.read .rsp).toNat 8
  /-- the argument area is as at `main`'s entry -/
  kargs : Keeps W.args s.m.memory s1.m.memory
  rip : x.m.core.rip = b + 0x2820#64
  rbp : x.m.core.read .rbp = s.m.core.read .rsp - 8#64
  r12 : BitVec.setWidth 32 (x.m.core.read .r12) = BitVec.setWidth 32 (s.m.core.read .rdi)
  rbx : x.m.core.read .rbx = s.m.core.read .rsi
  r14 : x.m.core.read .r14 = b + 0x71af#64
  r15 : x.m.core.read .r15 = b + 0x9a20#64
  guard : x.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  g : x.g = s.g
  env : MEnv E W b lb C fi sto ste sti x.m.memory
  rw : ShaRw b x.m.memory
  /-- the image below the option variables, and the kept memory outside the image, are as at
  `main`'s entry (bytes and permissions) -/
  kimg : Keeps (fun a => ImgW b a ∨ (W.Kept a ∧ ¬ ShaImg b a)) s.m.memory s1.m.memory
  /-- `have_read_stdin` (`.bss` `0xa160`, not written by the head) is as at `main`'s entry -/
  khr : s1.m.memory.readBytes (b.toNat + 0xa160) 1 = s.m.memory.readBytes (b.toNat + 0xa160) 1

theorem loadN_store8L {m : Memory} {a v : Word} (hr : m.Permitted .read a.toNat 8) :
    loadN (storeMem m a 8 v) a 8 = some v := by
  simp only [loadN, storeMem_read hr, Option.map_some, Silmaril.X86.Ext.leValue_leBytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [v.isLt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`main` from `0x27cb` to `0x2820`**, with `program_invocation_name = argv[0]` (K8). -/
theorem sha_main_localeP {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none) (L : LocImps E W lb) (hpk : PrivKeep E)
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s v : PState} {g a0p : Word}
    (hS : MainSpn E W b lb kb sr sc C fi sto ste sti s v g a0p) (hrw : ShaRw b v.m.memory)
    (hal : (s.m.core.read .rsp).toNat % 16 = 8) (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hpinC : ∀ a, PinR lb a → C a) (hpinK : ∀ a, PinR lb a → ¬ W.Kept a)
    (hlb : lb.toNat + 0x2056b0 < 2 ^ 64) (hImgVar : ∀ a, ShaImg b a → ¬ VarR lb a)
    (hArgsImg : ∀ a, W.args a → ¬ ShaImg b a)
    (k : ∀ s1 x, MainLoc E W b lb kb sr sc C fi sto ste sti s s1 x g →
      loadN x.m.memory (lb + 0x205378#64) 8 = some a0p → MustQ W Q x) : MustQ W Q v := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I hb hn
  have hB := hS.body
  have hroom := hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hd := hB.done
  have hMk := shaMemAll_keepI (lb := lb) (kb := kb) (sr := sr) (sc := sc) I hb
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a := by
    intro a ha
    by_contra hc
    exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  have hImgK : ∀ a, ShaImg b a → W.Kept a := fun a h => Or.inl (by rw [I]; exact h)
  -- o = 123: rax := &program_invocation_name
  refine must_listed (o := 123) shaM_listing_ok.1 rfl hd (by rw [hS.rip]; exact hin _ (by decide))
    hB.mem.mn.mainA (by rw [hS.rip, ripadd]) ?_
  xstep [hS.rip, hB.mem.mn.pinV]
  refine must_gen (fun w => w.m.core.rip = b + 0x27d2#64 ∧ w.m.memory = v.m.memory ∧ w.g = v.g ∧
      w.m.core.read .rax = lb + 0x205378#64 ∧ w.m.core.fsBase = v.m.core.fsBase ∧
      (∀ r, r ≠ .rax → w.m.core.read r = v.m.core.read r)) ?_ ?_
  · exact ⟨by simp, rfl, rfl, by simp, rfl, fun r h => by simp [h]⟩
  rintro w ⟨hrw', hmw, hgw, haxw, hfsw, hregw⟩
  have hdw : w.g.done = none := by rw [hgw]; exact hd
  -- o = 130: program_name := argv[0]
  have hA1 : w.m.core.rip + BitVec.ofNat 64 7 + BitVec.signExtend 64 0x79a7#32 = b + 0xa180#64 := by
    rw [hrw', BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hA1n : (b + 0xa180#64).toNat = b.toNat + 0xa160 + 0x20 := by
    rw [addr_toNat (by omega)]
  have pw1 : w.m.memory.Permitted .write (w.m.core.rip + BitVec.ofNat 64 7 + BitVec.signExtend 64 0x79a7#32).toNat 8 := by
    rw [hA1, hA1n, hmw]
    exact permitted_of (by omega) fun j hj => by rw [Nat.add_assoc]; exact (hrw (0x20 + j) (by omega)).2
  refine must_listed (o := 130) shaM_listing_ok.1 rfl hdw (by rw [hrw']; exact hin _ (by decide))
    (by rw [hmw]; exact hB.mem.mn.mainA) (by rw [hrw', ripadd]) ?_
  rw [exec_storeq_rip _ _ _ _ _ pw1, WP_ok, hA1]
  have h13w : w.m.core.read .r13 = a0p := by rw [hregw _ (by decide), hS.r13]
  rw [h13w]
  set m1 := storeMem w.m.memory (b + 0xa180#64) 8 a0p with hm1
  have hm1img : ShaMemAll b lb kb sr sc m1 := by
    rw [hm1, hmw]
    exact hB.mem.keepW hb (storeMem_keeps fun x hx => by
      obtain ⟨⟨h1, h2⟩, h3⟩ := hx; rw [hA1n]; omega)
  refine must_listed (o := 137) shaM_listing_ok.1 rfl hdw (by simp only [hrw', ripadd]; exact hin _ (by decide))
    hm1img.mn.mainA (by simp only [hrw', ripadd]) ?_
  xstep [hrw']
  refine must_listed (o := 144) shaM_listing_ok.1 rfl hdw (hin _ (by decide)) hm1img.mn.mainA (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 149) shaM_listing_ok.1 rfl hdw (hin _ (by decide)) hm1img.mn.mainA (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 156) shaM_listing_ok.1 rfl hdw (hin _ (by decide)) hm1img.mn.mainA (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun y => y.m.core.rip = b + 0x27f3#64 ∧ y.m.memory = m1 ∧ y.g = v.g ∧
      y.m.core.read .rax = lb + 0x205378#64 ∧ y.m.core.read .r13 = a0p ∧
      y.m.core.read .r14 = b + 0x71af#64 ∧ y.m.core.read .r15 = b + 0x9a20#64 ∧
      y.m.core.fsBase = v.m.core.fsBase ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → r ≠ .r14 → r ≠ .r15 → y.m.core.read r = v.m.core.read r)) ?_ ?_
  · refine ⟨by simp, rfl, hgw, by simp [haxw], by simp [h13w], by simp, by simp, by simp [hfsw], fun r h1 h2 h3 h4 h5 => ?_⟩
    simp [h2, h3, h4, h5, hregw r h1]
  rintro y ⟨hry, hmy, hgy, haxy, h13y, h14y, h15y, hfsy, hregy⟩
  have hdy : y.g.done = none := by rw [hgy]; exact hd
  -- o = 163: program_invocation_name := argv[0]
  have hpinN : (lb + 0x205378#64).toNat = lb.toNat + 0x205378 := addr_toNat (by omega)
  have hA2 : y.m.core.read .rax + BitVec.signExtend 64 0#32 = lb + 0x205378#64 := by
    rw [haxy]; simp
  have pw2 : y.m.memory.Permitted .write (y.m.core.read .rax + BitVec.signExtend 64 0#32).toNat 8 := by
    rw [hA2, hpinN, hmy, hm1, storeMem_permitted, hmw]
    exact permitted_of (by omega) fun j hj => hS.env.wr _ (hpinC _ ⟨by rw [hpinN]; omega, by rw [hpinN]; omega⟩)
  refine must_listed (o := 163) shaM_listing_ok.1 rfl hdy (by rw [hry]; exact hin _ (by decide))
    (by rw [hmy]; exact hm1img.mn.mainA) (by rw [hry, ripadd]) ?_
  rw [exec_storeq _ _ _ _ _ _ pw2, WP_ok, hA2, h13y]
  have pr2 : y.m.memory.Permitted .read (lb + 0x205378#64).toNat 8 := by
    rw [hpinN, hmy, hm1, storeMem_permitted, hmw]
    exact permitted_of (by omega) fun j hj =>
      (hS.env.np _ (Or.inr (hpinC _ ⟨by rw [hpinN]; omega, by rw [hpinN]; omega⟩))).2
  have hpin2 : loadN (storeMem y.m.memory (lb + 0x205378#64) 8 a0p) (lb + 0x205378#64) 8 = some a0p :=
    loadN_store8L pr2
  set m2 := storeMem y.m.memory (lb + 0x205378#64) 8 a0p with hm2
  -- the new base
  have hkm2 : Keeps (fun x => ImgW b x ∨ ((s.m.core.read .rsp).toNat - 4096 ≤ x ∧ x < (s.m.core.read .rsp).toNat + 8))
      v.m.memory m2 := by
    rw [hm2, hmy, hm1, hmw]
    refine (storeMem_keeps fun x hx => ?_).trans (storeMem_keeps fun x hx => ?_)
    · rw [hA1n]
      by_contra hc
      rcases hx with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
      · omega
      · have := hKout x (hImgK x ⟨by omega, by omega⟩); omega
    · rw [hpinN]
      by_contra hc
      have hP : PinR lb x := ⟨by rw [hpinN]; omega, by rw [hpinN]; omega⟩
      rcases hx with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact hpinK x hP (hImgK x h1)
      · have := hC x (hpinC x hP); omega
  have hka2 : Keeps W.args s.m.memory m2 := by
    refine (hB.keep.mono fun x hx => Or.inl (Or.inr (Or.inl hx))).trans ?_
    rw [hm2, hmy, hm1, hmw]
    refine (storeMem_keeps fun x hx => ?_).trans (storeMem_keeps fun x hx => ?_)
    · rw [hA1n]; by_contra hc; exact hArgsImg x hx ⟨by omega, by omega⟩
    · rw [hpinN]; by_contra hc
      exact hpinK x ⟨by rw [hpinN]; omega, by rw [hpinN]; omega⟩ (Or.inr (Or.inl hx))
  have hperm2 : ∀ x acc, m2.permits acc x = v.m.memory.permits acc x := by
    intro x acc; rw [hm2, hmy, hm1, hmw]; rfl
  obtain ⟨hB2, hret2⟩ := body_rebase hb hB (fun p hp => by
      have := sv6_bound8 s p hp; exact ⟨this.1, by omega⟩) hkm2 hperm2
    (c := { y.m.core with rip := y.m.core.rip + BitVec.ofNat 64 3 }) (by simp [hregy .rsp (by decide) (by decide)
      (by decide) (by decide) (by decide)]) (by simp [hfsy])
  set s1 : PState := ⟨⟨s.m.core, m2⟩, s.g⟩ with hs1
  have henv2 : MEnv E W b lb C fi sto ste sti m2 := by
    have h1 : MEnv E W b lb C fi sto ste sti m1 := by
      rw [hm1, hmw]
      refine hS.env.store hpk fun x h1 h2 => ?_
      rw [hA1n] at h1 h2
      have hi : ShaImg b x := ⟨by omega, by omega⟩
      exact ⟨(hS.env.np x (Or.inl hi)).1, hImgVar x hi⟩
    rw [hm2, hmy]
    refine h1.store hpk fun x h1' h2' => ?_
    rw [hpinN] at h1' h2'
    have hP : PinR lb x := ⟨by rw [hpinN]; omega, by rw [hpinN]; omega⟩
    refine ⟨(h1.np x (Or.inr (hpinC x hP))).1, fun ⟨h3, h4⟩ => ?_⟩
    have : (lb + 0x2056a0#64).toNat = lb.toNat + 0x2056a0 := addr_toNat (by omega)
    omega
  have hrw2 : ShaRw b m2 := fun j hj => by rw [hperm2, hperm2]; exact hrw j hj
  have hguard2 : m2.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [g]) := by
    rw [hkm2.readBytes (fun j hj => Or.inr ⟨by omega, by omega⟩)]; exact hS.guard
  have hsp1 : s1.m.core.read .rsp = s.m.core.read .rsp := rfl
  -- o = 166: r13 := "coreutils"; setlocale (LC_ALL, "")
  refine must_listed (o := 166) shaM_listing_ok.1 rfl hdy (by rw [hry, ripadd]; exact hin _ (by decide))
    hB2.mem.mn.mainA (by simp only [hry, ripadd]) ?_
  xstep [hry]
  refine main_callC I hb hlz (s := s1) (hB2.of_eq rfl (by simp) (by simp) (by rw [hgy])) hal hlo hC henv2
    shaM_listing_ok.1 (fun m h => h.mn.mainA) (o := 173) rfl (hin _ (by decide)) (by simp only [ripadd])
    (so := 0x140) rfl rfl (by simp only [BitVec.add_assoc]; rfl) (by decide) L.setlocale
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x140 + 4 + 6) + BitVec.signExtend 64 0x796e#32 = b + 0x9e78#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.mn.setlocale)
    (fun r h => framedQuiet_imp h) (fun he _ => he) (fun x h => h.elim) ?_
  intro x1 _ hB3 hrx1 hspx1 hcsx1 hgx1 henvx1 hkx1 hkc1
  have hdx1 : x1.g.done = none := hB3.done
  -- bindtextdomain ("coreutils", "/usr/share/locale")
  refine must_listed (o := 178) shaM_listing_ok.1 rfl hdx1 (by rw [hrx1]; exact img_off I hb (by decide))
    hB3.mem.mn.mainA (by rw [hrx1]) ?_
  xstep [hrx1]
  refine must_listed (o := 185) shaM_listing_ok.1 rfl hdx1 (hin _ (by decide)) hB3.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep []
  refine main_callC I hb hlz (s := s1) (hB3.of_eq rfl (by simp) (by simp) rfl) hal hlo hC henvx1
    shaM_listing_ok.1 (fun m h => h.mn.mainA) (o := 188) rfl (hin _ (by decide)) (by simp only [ripadd])
    (so := 0x170) rfl rfl (by simp only [BitVec.add_assoc]; rfl) (by decide) L.bindtextdomain
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x170 + 4 + 6) + BitVec.signExtend 64 0x7956#32 = b + 0x9e90#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.mn.bindtextdomain)
    (fun r h => framedQuiet_imp h) (fun he _ => he) (fun x h => h.elim) ?_
  intro x2 _ hB4 hrx2 hspx2 hcsx2 hgx2 henvx2 hkx2 hkc2
  have hdx2 : x2.g.done = none := hB4.done
  -- textdomain ("coreutils")
  refine must_listed (o := 193) shaM_listing_ok.1 rfl hdx2 (by rw [hrx2]; exact img_off I hb (by decide))
    hB4.mem.mn.mainA (by rw [hrx2]) ?_
  xstep [hrx2]
  refine must_listed (o := 196) shaM_listing_ok.1 rfl hdx2 (hin _ (by decide)) hB4.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep []
  refine main_callC I hb hlz (s := s1) (hB4.of_eq rfl (by simp) (by simp) rfl) hal hlo hC henvx2
    shaM_listing_ok.1 (fun m h => h.mn.mainA) (o := 203) rfl (hin _ (by decide)) (by simp only [ripadd])
    (so := 0x280) rfl rfl (by simp only [BitVec.add_assoc]; rfl) (by decide) L.textdomain
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x280 + 4 + 6) + BitVec.signExtend 64 0x78ce#32 = b + 0x9f18#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.mn.textdomain)
    (fun r h => framedQuiet_imp h) (fun he _ => he) (fun x h => h.elim) ?_
  intro x3 _ hB5 hrx3 hspx3 hcsx3 hgx3 henvx3 hkx3 hkc3
  have hreg3 : ∀ r, r ∈ Silmaril.X86.sysv64.calleeSaved → r ≠ .r13 →
      x3.m.core.read r = y.m.core.read r := by
    intro r hr hne
    have hdi : r ≠ .rdi := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    have hsi : r ≠ .rsi := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    rw [hcsx3 r hr]
    simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other _ _ _ _ hne,
      Silmaril.Machine.RegisterFile.write_other _ _ _ _ hdi,
      st_regs_apply]
    rw [hcsx2 r hr]
    simp only [st_read_mk,
      Silmaril.Machine.RegisterFile.write_other _ _ _ _ hdi, Silmaril.Machine.RegisterFile.write_other _ _ _ _ hsi,
      st_regs_apply]
    rw [hcsx1 r hr]
    simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other _ _ _ _ hne, st_regs_apply]
  have cs : ∀ r, r ∈ Silmaril.X86.sysv64.calleeSaved → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 →
      x3.m.core.read r = v.m.core.read r := fun r hr h13 h14 h15 => by
    rw [hreg3 r hr h13, hregy r (by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr)
      (by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr)
      (by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr) h14 h15]
  have hk13 : Keeps (fun x => W.Kept x ∨ (s.m.core.read .rsp).toNat - 328 ≤ x) m2 x3.m.memory :=
    ((hkx1.mono fun x hx => ⟨hx, fun h => h⟩).trans ((hkx2.mono fun x hx => ⟨hx, fun h => h⟩).trans
      (hkx3.mono fun x hx => ⟨hx, fun h => h⟩)))
  have hki2 : Keeps (fun x => ImgW b x ∨ (W.Kept x ∧ ¬ ShaImg b x)) s.m.memory m2 := by
    refine (hB.keep.mono fun x hx => Or.inl ?_).trans ?_
    · rcases hx with h | h
      · exact hImgK x h.1
      · exact h.1
    · rw [hm2, hmy, hm1, hmw]
      refine (storeMem_keeps fun x hx => ?_).trans (storeMem_keeps fun x hx => ?_)
      · rw [hA1n]; by_contra hc
        rcases hx with ⟨⟨h1, h2⟩, h3⟩ | ⟨-, h4⟩
        · omega
        · exact h4 ⟨by omega, by omega⟩
      · rw [hpinN]; by_contra hc
        have hP : PinR lb x := ⟨by rw [hpinN]; omega, by rw [hpinN]; omega⟩
        rcases hx with ⟨h1, -⟩ | ⟨h5, -⟩
        · exact hpinK x hP (hImgK x h1)
        · exact hpinK x hP h5
  have hhr2 : m2.readBytes (b.toNat + 0xa160) 1 = s.m.memory.readBytes (b.toNat + 0xa160) 1 := by
    refine Keeps.readBytes (P := fun x => x = b.toNat + 0xa160) ?_ (fun j hj => by omega)
    refine (hB.keep.mono fun x hx => Or.inl (hImgK x ⟨by omega, by omega⟩)).trans ?_
    rw [hm2, hmy, hm1, hmw]
    refine (storeMem_keeps fun x hx => ?_).trans (storeMem_keeps fun x hx => ?_)
    · rw [hA1n]; omega
    · rw [hpinN]; by_contra hc
      have hP : PinR lb x := ⟨by rw [hpinN]; omega, by rw [hpinN]; omega⟩
      exact hpinK x hP (hImgK x ⟨by omega, by omega⟩)
  have hpin3 : loadN x3.m.memory (lb + 0x205378#64) 8 = some a0p := by
    rw [loadN_keeps (hkc1.trans (hkc2.trans hkc3)) (fun j hj => hpinC _ ⟨by omega, by omega⟩)]; exact hpin2
  refine k s1 x3 ⟨hB5, rfl, rfl, hret2, hka2, by rw [hrx3, BitVec.add_assoc]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, henvx3, ?_,
    hki2, hhr2⟩ hpin3
  · rw [cs .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide) (by decide) (by decide)]; exact hS.rbp
  · rw [cs .r12 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide) (by decide) (by decide)]; exact hS.r12
  · rw [cs .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide) (by decide) (by decide)]; exact hS.rbx
  · rw [hreg3 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact h14y
  · rw [hreg3 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact h15y
  · rw [hk13.readBytes (fun j hj => Or.inr (by omega))]; exact hguard2
  · rw [hgx3, hgx2, hgx1]; simp [hgy, hS.g]
  · intro j hj
    have hi : W.Kept (b.toNat + 0xa160 + j) := hImgK _ ⟨by omega, by omega⟩
    rw [(hk13 _ (Or.inl hi)).2, (hk13 _ (Or.inl hi)).2]
    exact hrw2 j hj

/-- **`main` from `0x27cb` to `0x2820`.** -/
theorem sha_main_locale {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none) (L : LocImps E W lb) (hpk : PrivKeep E)
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s v : PState} {g a0p : Word}
    (hS : MainSpn E W b lb kb sr sc C fi sto ste sti s v g a0p) (hrw : ShaRw b v.m.memory)
    (hal : (s.m.core.read .rsp).toNat % 16 = 8) (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hpinC : ∀ a, PinR lb a → C a) (hpinK : ∀ a, PinR lb a → ¬ W.Kept a)
    (hlb : lb.toNat + 0x2056b0 < 2 ^ 64) (hImgVar : ∀ a, ShaImg b a → ¬ VarR lb a)
    (hArgsImg : ∀ a, W.args a → ¬ ShaImg b a)
    (k : ∀ s1 x, MainLoc E W b lb kb sr sc C fi sto ste sti s s1 x g → MustQ W Q x) : MustQ W Q v :=
  sha_main_localeP I hb hlz L hpk hS hrw hal hlo hC hpinC hpinK hlb hImgVar hArgsImg fun s1 x h _ => k s1 x h

end Silmaril.Elf.Link.Dyn.Sha256sum
