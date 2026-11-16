module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainOpt

/-! # GNU `sha256sum`: `main`'s option flags and `getopt_long`

`0x2844`–`0x29fd`: `binary = -1`, `do_check = false` and the `--tag` flag in the frame, then
`getopt_long (argc, argv, "bctwz", long_options, NULL)`; on an argument vector without options it
returns `-1` at once (with `optind = 1`) and `main` leaves the option loop for `0x29fd`.
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

/-- What holds at `0x29fd`: the body (with `optind` no longer among the cells `C`), the three
option flags in the frame, and `optind = 1`. -/
structure MainOpt (E : Env) (W : World) (b lb kb sr sc : Word) (C : Nat → Prop) (fi : Word)
    (sto ste sti : St) (s s1 z : PState) (g : Word) (G : Ghost) : Prop where
  at_ : MainAt E W b lb kb sr sc (fun a => C a ∧ ¬ OptR E a) fi sto ste sti s s1 z g (b + 0x29fd#64) G
  tag : z.m.memory.readBytes ((s.m.core.read .rsp).toNat - 216) 1 = some [0#8]
  binary : z.m.memory.readBytes ((s.m.core.read .rsp).toNat - 208) 4 = some [0xff#8, 0xff#8, 0xff#8, 0xff#8]
  check : z.m.memory.readBytes ((s.m.core.read .rsp).toNat - 232) 1 = some [0#8]
  optind : loadN z.m.memory E.optindA 4 = some 1#64

theorem contract_post {pre : Prop} {Q Q' : PState → Prop} {r : Silmaril.X86.RelIsa.Res PState}
    (h : Contract pre Q r) (hq : ∀ t, Q t → Q' t) : Contract pre Q' r := fun hp => by
  obtain ⟨t, ht, h'⟩ := h hp
  exact ⟨t, ht, hq t h'⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The option flags and `getopt_long` returning `-1`** (`0x2844`–`0x29fd`), keeping the cells `C`
but `optind` (K8). -/
theorem sha_main_getoptP {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hG : ImpOk W (lb + 0xf5ad0#64) (nm "getopt_long") (getoptNoneStep E W))
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s s1 y : PState} {g : Word} {G : Ghost}
    (hM : MainAt E W b lb kb sr sc C fi sto ste sti s s1 y g (b + 0x2844#64) G)
    (hal : (s.m.core.read .rsp).toNat % 16 = 8) (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hoptC : ∀ a, OptR E a → C a) (hoptK : ∀ a, OptR E a → ¬ W.Kept a)
    (hoptL : ∀ a, OptR E a → a + 48 < (s.m.core.read .rsp).toNat) (hopt : E.optindA.toNat + 4 < 2 ^ 64)
    {args : List (List Byte)} (hargc : (BitVec.setWidth 32 (s.m.core.read .rdi)).toNat = args.length)
    (hargv : ∀ m, Keeps W.args s.m.memory m → Argv m (s.m.core.read .rsi) args)
    (hdash : ∀ a ∈ args.drop 1, a.head? ≠ some 0x2d#8)
    (k : ∀ z, MainOpt E W b lb kb sr sc C fi sto ste sti s s1 z g G →
      Keeps (fun a => C a ∧ ¬ OptR E a) y.m.memory z.m.memory → MustQ W Q z) : MustQ W Q y := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I hb hn
  have hB := hM.body
  have hsp1 : s1.m.core.read .rsp = s.m.core.read .rsp := by rw [hM.base]
  have hroom : Room W y.m.memory (s.m.core.read .rsp) 4096 := hsp1 ▸ hB.room
  have hsp := hroom.1
  have hd := hB.done
  have hMk := shaMemAll_keepI (lb := lb) (kb := kb) (sr := sr) (sc := sc) I hb
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a := by
    intro a ha; by_contra hc; exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  have hvk : ∀ x, VarR lb x → W.Kept x := fun x hx => by
    obtain ⟨h1, h2⟩ := hx
    have := hM.env.vars.kept (x - (lb + 0x2056a0#64).toNat) (by omega)
    rwa [show (lb + 0x2056a0#64).toNat + (x - (lb + 0x2056a0#64).toNat) = x by omega] at this
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have aoff : ∀ (d : BitVec 32) (k : Nat), BitVec.signExtend 64 d = BitVec.ofNat 64 (2 ^ 64 - k) → 8 ≤ k → k < 4096 →
      (y.m.core.read .rbp + BitVec.signExtend 64 d).toNat = (s.m.core.read .rsp).toNat - 8 - k := by
    intro d k hd hk1 hk2
    rw [hM.rbp, hd, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  -- a store into the frame at `A` (`k` bytes), as a body and an environment
  have fstore : ∀ (m : Memory) (A v : Word) (n : Nat), (s.m.core.read .rsp).toNat - 328 ≤ A.toNat →
      A.toNat + n + 48 ≤ (s.m.core.read .rsp).toNat → MEnv E W b lb C fi sto ste sti m →
      MEnv E W b lb C fi sto ste sti (storeMem m A n v) := by
    intro m A v n h1 h2 hE
    refine hE.store (privKeep E) fun x hx1 hx2 => ⟨fun hp => ?_, fun hv => ?_⟩
    · have := E.S.priv_lo _ _ hp; omega
    · have := hKout x (hvk x hv); omega
  -- the three flags
  have a1 := aoff 0xffffff30#32 208 (by decide) (by decide) (by decide)
  have pw1 : y.m.memory.Permitted .write (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff30#32).toNat 1 := by
    rw [a1]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  refine must_listed (o := 244) shaM_listing_ok.1 rfl hd (by rw [hM.rip]; exact hin _ (by decide))
    hB.mem.mn.mainA (by rw [hM.rip, ripadd]) ?_
  rw [exec_storeb_d _ _ _ _ _ _ pw1, WP_ok]
  set m1 := storeMem y.m.memory (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff30#32) 1 ((0#8).setWidth 64)
    with hm1
  have hB1 : Body W (ShaMemAll b lb kb sr sc) s1 ⟨⟨{ y.m.core with rip := y.m.core.rip + BitVec.ofNat 64 7 }, m1⟩, y.g⟩
      328 4096 (sv6 s1) :=
    BodyX.store hMk hB (by decide) (fun p hp => (sv6_bound328 s1 p hp).1) (by rw [a1, hsp1]; omega)
      (by rw [a1, hsp1]; omega) rfl (by simp) rfl rfl
  have hE1 : MEnv E W b lb C fi sto ste sti m1 := fstore _ _ _ _ (by rw [a1]; omega) (by rw [a1]; omega) hM.env
  refine must_gen (fun v => v.m.core.rip = b + 0x284b#64 ∧ v.m.memory = m1 ∧ v.g = y.g ∧
      v.m.core.fsBase = y.m.core.fsBase ∧ ∀ r, v.m.core.read r = y.m.core.read r) ?_ ?_
  · exact ⟨by rw [hM.rip, ripadd], rfl, rfl, rfl, fun r => rfl⟩
  rintro v1 ⟨hr1, hmv1, hg1, hf1, hreg1⟩
  have hd1 : v1.g.done = none := by rw [hg1]; exact hd
  have hBv1 : Body W (ShaMemAll b lb kb sr sc) s1 v1 328 4096 (sv6 s1) :=
    hB1.of_eq hmv1 (hreg1 .rsp) hf1 (by rw [hg1])
  have a2 := aoff 0xffffff38#32 200 (by decide) (by decide) (by decide)
  have pw2 : v1.m.memory.Permitted .write (v1.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32).toNat 4 := by
    rw [hreg1, a2, hmv1, hm1, storeMem_permitted]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  refine must_listed (o := 251) shaM_listing_ok.1 rfl hd1 (by rw [hr1]; exact hin _ (by decide))
    hBv1.mem.mn.mainA (by rw [hr1, ripadd]) ?_
  rw [exec_storeI32_d _ _ _ _ _ _ pw2, WP_ok]
  set m2 := storeMem v1.m.memory (v1.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32) 4
    (((0xffffffff#32).signExtend 32).setWidth 64) with hm2
  have hrbp1 : v1.m.core.read .rbp = y.m.core.read .rbp := hreg1 .rbp
  have hB2 : Body W (ShaMemAll b lb kb sr sc) s1 ⟨⟨{ v1.m.core with rip := v1.m.core.rip + BitVec.ofNat 64 10 }, m2⟩, v1.g⟩
      328 4096 (sv6 s1) :=
    BodyX.store hMk hBv1 (by decide) (fun p hp => (sv6_bound328 s1 p hp).1) (by rw [hrbp1, a2, hsp1]; omega)
      (by rw [hrbp1, a2, hsp1]; omega) rfl (by simp) rfl rfl
  have hE2 : MEnv E W b lb C fi sto ste sti m2 :=
    fstore _ _ _ _ (by rw [hrbp1, a2]; omega) (by rw [hrbp1, a2]; omega) (by rw [hmv1]; exact hE1)
  refine must_gen (fun v => v.m.core.rip = b + 0x2855#64 ∧ v.m.memory = m2 ∧ v.g = y.g ∧
      v.m.core.fsBase = y.m.core.fsBase ∧ ∀ r, v.m.core.read r = y.m.core.read r) ?_ ?_
  · exact ⟨by rw [hr1, ripadd], rfl, hg1, hf1, fun r => hreg1 r⟩
  rintro v2 ⟨hr2, hmv2, hg2, hf2, hreg2⟩
  have hd2 : v2.g.done = none := by rw [hg2]; exact hd
  have hBv2 : Body W (ShaMemAll b lb kb sr sc) s1 v2 328 4096 (sv6 s1) :=
    hB2.of_eq hmv2 (by rw [hreg2 .rsp]; exact (hreg1 .rsp).symm) (by rw [hf2, hf1]) (by rw [hg2, hg1])
  have a3 := aoff 0xffffff20#32 224 (by decide) (by decide) (by decide)
  have pw3 : v2.m.memory.Permitted .write (v2.m.core.read .rbp + BitVec.signExtend 64 0xffffff20#32).toNat 1 := by
    rw [hreg2, a3, hmv2, hm2, storeMem_permitted, hmv1, hm1, storeMem_permitted]
    exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  refine must_listed (o := 261) shaM_listing_ok.1 rfl hd2 (by rw [hr2]; exact hin _ (by decide))
    hBv2.mem.mn.mainA (by rw [hr2, ripadd]) ?_
  rw [exec_storeb_d _ _ _ _ _ _ pw3, WP_ok]
  have hrbp2 : v2.m.core.read .rbp = y.m.core.read .rbp := hreg2 .rbp
  set m3 := storeMem v2.m.memory (v2.m.core.read .rbp + BitVec.signExtend 64 0xffffff20#32) 1 ((0#8).setWidth 64)
    with hm3
  have hB3 : Body W (ShaMemAll b lb kb sr sc) s1 ⟨⟨{ v2.m.core with rip := v2.m.core.rip + BitVec.ofNat 64 7 }, m3⟩, v2.g⟩
      328 4096 (sv6 s1) :=
    BodyX.store hMk hBv2 (by decide) (fun p hp => (sv6_bound328 s1 p hp).1) (by rw [hrbp2, a3, hsp1]; omega)
      (by rw [hrbp2, a3, hsp1]; omega) rfl (by simp) rfl rfl
  have hE3 : MEnv E W b lb C fi sto ste sti m3 :=
    fstore _ _ _ _ (by rw [hrbp2, a3]; omega) (by rw [hrbp2, a3]; omega) (by rw [hmv2]; exact hE2)
  refine must_gen (fun v => v.m.core.rip = b + 0x285c#64 ∧ v.m.memory = m3 ∧ v.g = y.g ∧
      v.m.core.fsBase = y.m.core.fsBase ∧ ∀ r, v.m.core.read r = y.m.core.read r) ?_ ?_
  · exact ⟨by rw [hr2, ripadd], rfl, hg2, hf2, fun r => hreg2 r⟩
  rintro v3 ⟨hr3, hmv3, hg3, hf3, hreg3⟩
  have hd3 : v3.g.done = none := by rw [hg3]; exact hd
  have hBv3 : Body W (ShaMemAll b lb kb sr sc) s1 v3 328 4096 (sv6 s1) :=
    hB3.of_eq hmv3 (by rw [hreg3 .rsp]; exact (hreg2 .rsp).symm) (by rw [hf3, hf2]) (by rw [hg3, hg2])
  refine must_listed (o := 268) shaM_listing_ok.1 rfl hd3 (by rw [hr3]; exact hin _ (by decide))
    hBv3.mem.mn.mainA (by rw [hr3, ripadd]) ?_
  xstep [hr3]
  refine must_listed (o := 272) shaM_listing_ok.1 rfl hd3 (hin _ (by decide)) hBv3.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep []
  refine must_listed (o := 275) shaM_listing_ok.1 rfl hd3 (hin _ (by decide)) hBv3.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep []
  refine must_listed (o := 278) shaM_listing_ok.1 rfl hd3 (hin _ (by decide)) hBv3.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep []
  refine must_listed (o := 281) shaM_listing_ok.1 rfl hd3 (hin _ (by decide)) hBv3.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep []
  refine must_listed (o := 284) shaM_listing_ok.1 rfl hd3 (hin _ (by decide)) hBv3.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep []
  refine must_gen (fun u => u.m.core.rip = b + 0x286f#64 ∧ u.m.memory = v3.m.memory ∧ u.g = y.g ∧
      u.m.core.fsBase = y.m.core.fsBase ∧
      BitVec.setWidth 32 (u.m.core.read .rdi) = BitVec.setWidth 32 (s.m.core.read .rdi) ∧
      u.m.core.read .rsi = s.m.core.read .rsi ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → u.m.core.read r = y.m.core.read r)) ?_ ?_
  · refine ⟨by simp, rfl, hg3, hf3, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_⟩
    · simp [hreg3, hM.r12]
    · simp [hreg3, hM.rbx]
    · simp [h1, h2, h3, h4, h5, hreg3]
  rintro u ⟨hru, hmu, hgu, hfu, hdiu, hsiu, hregu⟩
  have hdu : u.g.done = none := by rw [hgu]; exact hd
  have hspu : u.m.core.read .rsp = y.m.core.read .rsp := hregu .rsp (by decide) (by decide) (by decide) (by decide) (by decide)
  have hBu : Body W (ShaMemAll b lb kb sr sc) s1 u 328 4096 (sv6 s1) :=
    hBv3.of_eq hmu (by rw [hspu, hreg3]) (by rw [hfu, hf3]) (by rw [hgu, hg3])
  have hEu : MEnv E W b lb C fi sto ste sti u.m.memory := by rw [hmu, hmv3]; exact hE3
  have hka : Keeps W.args s.m.memory u.m.memory :=
    hM.kargs.trans (hBu.keep.mono fun x hx => Or.inl (Or.inr (Or.inl hx)))
  have hoptP : ∀ j, j < 4 → u.m.memory.permits .read (E.optindA.toNat + j) = true ∧
      u.m.memory.permits .write (E.optindA.toNat + j) = true := fun j hj =>
    ⟨(hEu.np _ (Or.inr (hoptC _ ⟨by omega, by omega⟩))).2, hEu.wr _ (hoptC _ ⟨by omega, by omega⟩)⟩
  have hwu : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 328 := by
    rw [hBu.rsp, hsp1]; exact sub_toNat (by omega) (by omega)
  have hu8 : (u.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 336 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hwu]; omega
  refine main_callC I hb hlz (s := s1) hBu (by rw [hsp1]; exact hal) (by rw [hsp1]; exact hlo)
    (C := fun a => C a ∧ ¬ OptR E a) (by rw [hsp1]; exact fun a h => hC a h.1)
    (hEu.mono fun a h => h.1)
    shaM_listing_ok.1 (fun m h => h.mn.mainA) (o := 287) rfl (by rw [hru]; exact hin _ (by decide))
    (by rw [hru, BitVec.add_assoc]; rfl)
    (so := 0x2c0) rfl rfl (by simp only [BitVec.add_assoc]; rfl) (by decide) hG
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x2c0 + 4 + 6) + BitVec.signExtend 64 0x78ae#32 = b + 0x9f38#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.mn.getopt)
    (R := fun t => BitVec.setWidth 32 (t.m.core.read .rax) = 0xffffffff#32 ∧
      loadN t.m.memory E.optindA 4 = some 1#64)
    (fp := fun a => E.optindA.toNat ≤ a ∧ a < E.optindA.toNat + 4)
    (fun r h => contract_post h fun t ⟨hl, hg', ho, hr, hi⟩ => ⟨hl, ho, hg', hr, hi⟩)
    (fun he _ => ⟨he, by rw [callEntry_mem, pushMem_permitted]; exact permitted_of (by omega) fun j hj => (hoptP j hj).1,
      by rw [callEntry_mem, pushMem_permitted]; exact permitted_of (by omega) fun j hj => (hoptP j hj).2,
      args, by rw [callEntry_read _ _ _ (by decide)]; exact (congrArg BitVec.toNat hdiu).trans hargc |>.symm,
      by
        rw [callEntry_mem, callEntry_read _ _ _ (by decide), hsiu]
        exact hargv _ (hka.trans (pushMem_keeps fun x hx => by
          rw [hu8]; by_contra hc
          exact (hroom.2.2 x (by omega) (by omega)).2.2 (Or.inr (Or.inl hx)))),
      hdash⟩)
    (fun x h => ⟨fun hk => hoptK x h hk, fun hc => hc.2 h, by rw [hsp1]; exact hoptL x h⟩) ?_
  intro z hRz hBz hrz hspz hcsz hgz henvz hkz hkcz
  obtain ⟨hraxz, hoptz⟩ := hRz
  have hdz : z.g.done = none := hBz.done
  have hje : Silmaril.X86.Ext.Cond.eval (cmpD (BitVec.setWidth 32 (z.m.core.read .rax)) 0xffffffff#32) .e = some true := by
    rw [eval_cmpD, hraxz]; decide
  have hje2 : Silmaril.X86.Ext.Cond.eval (@Silmaril.X86.Ext.AluOp.flagsN 32 Silmaril.X86.AluOp.cmp
      (BitVec.setWidth 32 (z.m.core.read .rax)) 4294967295#32) .e = some true := hje
  refine must_listed (o := 292) shaM_listing_ok.1 rfl hdz (by rw [hrz]; exact img_off I hb (by decide))
    hBz.mem.mn.mainA (by rw [hrz]) ?_
  xstep [hrz]
  refine must_listed (o := 295) shaM_listing_ok.1 rfl hdz (hin _ (by decide)) hBz.mem.mn.mainA (by simp only [ripadd]) ?_
  xstep [hje2]
  have hcsZ : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, z.m.core.read r = y.m.core.read r := by
    intro r hr
    rw [hcsz r hr]
    have h1 : r ≠ .rdi := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    have h2 : r ≠ .rsi := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    have h3 : r ≠ .rdx := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    have h4 : r ≠ .rcx := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    have h5 : r ≠ .r8 := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    exact hregu r h1 h2 h3 h4 h5
  have hoptOut : ∀ x, E.optindA.toNat ≤ x → x < E.optindA.toNat + 4 →
      x < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ x :=
    fun x h1 h2 => hC x (hoptC x ⟨h1, h2⟩)
  -- what the call keeps of the frame and the image, back to `y`
  have hkzu : Keeps (fun x => (W.Kept x ∨ (s.m.core.read .rsp).toNat - 328 ≤ x) ∧
      ¬ (E.optindA.toNat ≤ x ∧ x < E.optindA.toNat + 4)) u.m.memory z.m.memory := by
    rw [hsp1] at hkz; exact hkz
  have hmu3 : u.m.memory = storeMem (storeMem (storeMem y.m.memory
      (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff30#32) 1 ((0#8).setWidth 64))
      (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32) 4 (((0xffffffff#32).signExtend 32).setWidth 64))
      (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff20#32) 1 ((0#8).setWidth 64) := by
    rw [hmu, hmv3, hm3, hrbp2, hmv2, hm2, hrbp1, hmv1, hm1]
  have rdz : ∀ (A n : Nat), (s.m.core.read .rsp).toNat - 328 ≤ A → A + n ≤ (s.m.core.read .rsp).toNat →
      z.m.memory.readBytes A n = u.m.memory.readBytes A n := fun A n h1 h2 =>
    hkzu.readBytes (fun j hj => ⟨Or.inr (by omega), fun ⟨q1, q2⟩ => by have := hoptOut _ q1 q2; omega⟩)
  have prz : ∀ x, ShaImg b x → ∀ acc, z.m.memory.permits acc x = y.m.memory.permits acc x := by
    intro x hx acc
    have hK : W.Kept x := Or.inl (by rw [I]; exact hx)
    rw [(hkzu x ⟨Or.inl hK, fun ⟨q1, q2⟩ => hoptK x ⟨q1, q2⟩ hK⟩).2 acc, hmu3]; rfl
  have hrd : ∀ (m : Memory) (A : Word) (n : Nat) (v : Word), m.Permitted .read A.toNat n →
      (storeMem m A n v).readBytes A.toNat n = some (Silmaril.X86.Ext.leBytes v n) := fun m A n v h => storeMem_read h
  have r1 : y.m.memory.Permitted .read (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff30#32).toNat 1 := by
    rw [a1]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have r2 : y.m.memory.Permitted .read (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32).toNat 4 := by
    rw [a2]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have r3 : y.m.memory.Permitted .read (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff20#32).toNat 1 := by
    rw [a3]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hkcu : Keeps (fun a => C a ∧ ¬ OptR E a) y.m.memory u.m.memory := by
    rw [hmu3]
    refine ((storeMem_keeps fun x hx => ?_).trans (storeMem_keeps fun x hx => ?_)).trans
      (storeMem_keeps fun x hx => ?_)
    · have := hC x hx.1; rw [a1]; omega
    · have := hC x hx.1; rw [a2]; omega
    · have := hC x hx.1; rw [a3]; omega
  refine k _ ⟨⟨hBz.of_eq rfl (by simp) rfl rfl, hM.base, hM.bg, hM.ret, hM.kargs, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hgz, hgu, hM.g], henvz, ?_, hM.kimg, hM.khr⟩, ?_, ?_, ?_, hoptz⟩ (hkcu.trans hkcz)
  · show z.m.core.read .rbp = _
    rw [hcsZ .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hM.rbp
  · show BitVec.setWidth 32 (z.m.core.read .r12) = _
    rw [hcsZ .r12 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hM.r12
  · show z.m.core.read .rbx = _
    rw [hcsZ .rbx (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hM.rbx
  · show z.m.core.read .r14 = _
    rw [hcsZ .r14 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hM.r14
  · show z.m.core.read .r15 = _
    rw [hcsZ .r15 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hM.r15
  · show z.m.memory.readBytes _ 8 = _
    rw [rdz _ _ (by omega) (by omega), hmu3, storeMem_read_ne (by rw [a3]; omega),
      storeMem_read_ne (by rw [a2]; omega), storeMem_read_ne (by rw [a1]; omega)]
    exact hM.guard
  · intro j hj
    have hx : ShaImg b (b.toNat + 0xa160 + j) := ⟨by omega, by omega⟩
    show z.m.memory.permits _ _ = true ∧ z.m.memory.permits _ _ = true
    rw [prz _ hx, prz _ hx]; exact hM.rw j hj
  · show z.m.memory.readBytes _ 1 = _
    rw [rdz _ _ (by omega) (by omega), hmu3, storeMem_read_ne (by rw [a3]; omega),
      storeMem_read_ne (by rw [a2]; omega), show (s.m.core.read .rsp).toNat - 216 =
        (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff30#32).toNat by rw [a1]; omega, hrd _ _ _ _ r1]
    decide
  · show z.m.memory.readBytes _ 4 = _
    rw [rdz _ _ (by omega) (by omega), hmu3, storeMem_read_ne (by rw [a3]; omega), show (s.m.core.read .rsp).toNat - 208 =
        (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32).toNat by rw [a2]; omega,
      hrd _ _ _ _ (by rw [storeMem_permitted]; exact r2)]
    decide
  · show z.m.memory.readBytes _ 1 = _
    rw [rdz _ _ (by omega) (by omega), hmu3, show (s.m.core.read .rsp).toNat - 232 =
        (y.m.core.read .rbp + BitVec.signExtend 64 0xffffff20#32).toNat by rw [a3]; omega,
      hrd _ _ _ _ (by rw [storeMem_permitted, storeMem_permitted]; exact r3)]
    decide

set_option maxRecDepth 100000 in
/-- **The option flags and `getopt_long` returning `-1`** (`0x2844`–`0x29fd`). -/
theorem sha_main_getopt {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hG : ImpOk W (lb + 0xf5ad0#64) (nm "getopt_long") (getoptNoneStep E W))
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s s1 y : PState} {g : Word} {G : Ghost}
    (hM : MainAt E W b lb kb sr sc C fi sto ste sti s s1 y g (b + 0x2844#64) G)
    (hal : (s.m.core.read .rsp).toNat % 16 = 8) (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hoptC : ∀ a, OptR E a → C a) (hoptK : ∀ a, OptR E a → ¬ W.Kept a)
    (hoptL : ∀ a, OptR E a → a + 48 < (s.m.core.read .rsp).toNat) (hopt : E.optindA.toNat + 4 < 2 ^ 64)
    {args : List (List Byte)} (hargc : (BitVec.setWidth 32 (s.m.core.read .rdi)).toNat = args.length)
    (hargv : ∀ m, Keeps W.args s.m.memory m → Argv m (s.m.core.read .rsi) args)
    (hdash : ∀ a ∈ args.drop 1, a.head? ≠ some 0x2d#8)
    (k : ∀ z, MainOpt E W b lb kb sr sc C fi sto ste sti s s1 z g G → MustQ W Q z) : MustQ W Q y :=
  sha_main_getoptP I hb hlz hG hM hal hlo hC hoptC hoptK hoptL hopt hargc hargv hdash fun z h _ => k z h

end Silmaril.Elf.Link.Dyn.Sha256sum
