module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainEnv

/-! # GNU `sha256sum`: `main` from its prologue through `set_program_name`'s `strrchr`

`0x2768`–`0x27cb`: `argv[0]` into `r13`, the stack guard into the frame (`[rbp - 0x38]`),
`argc`/`argv` into `r12`/`rbx`, and gnulib's `set_program_name (argv[0])` (inlined):
`strrchr (argv[0], '/')`. For a program name without `/` the result is `NULL` and the code
continues at `0x27cb` (the `/.libs/lt-` checks are skipped).
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
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

theorem sv6_bound328 (s : PState) : ∀ p ∈ sv6 s, p.1 ≤ 48 ∧ 48 ≤ 328 := by
  intro q hq
  simp only [sv6, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem cstr_keeps {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') {a : Word} {l : List Byte}
    (hc : CStr m a l) (hP : ∀ j, j < l.length + 1 → P (a.toNat + j)) : CStr m' a l :=
  ⟨hc.1, by rw [h.readBytes (fun j hj => hP j (by simpa using hj))]; exact hc.2⟩

/-- `strrchr (s, c)` finds no `c` in a string without it (and `c ≠ 0`). -/
theorem rfind_none {l : List Byte} {c : Byte} (hl : ∀ x ∈ l, x ≠ c) (hc : c ≠ 0#8) :
    (List.range (l.length + 1)).reverse.find? (fun i => (l ++ [(0 : Byte)])[i]? = some c) = none := by
  rw [List.find?_eq_none]
  intro i hi
  simp only [List.mem_reverse, List.mem_range] at hi
  simp only [decide_eq_true_eq]
  intro h
  by_cases hil : i < l.length
  · rw [List.getElem?_append_left hil, List.getElem?_eq_getElem hil, Option.some.injEq] at h
    exact hl _ (List.getElem_mem hil) h
  · have : i = l.length := by omega
    subst this
    simp at h
    exact hc h.symm

/-- What holds at `0x27cb`. -/
structure MainSpn (E : Env) (W : World) (b lb kb sr sc : Word) (C : Nat → Prop) (fi : Word)
    (sto ste sti : St) (s v : PState) (g a0p : Word) : Prop where
  body : Body W (ShaMemAll b lb kb sr sc) s v 328 4096 (sv6 s)
  rip : v.m.core.rip = b + 0x27cb#64
  rbp : v.m.core.read .rbp = s.m.core.read .rsp - 8#64
  r12 : BitVec.setWidth 32 (v.m.core.read .r12) = BitVec.setWidth 32 (s.m.core.read .rdi)
  rbx : v.m.core.read .rbx = s.m.core.read .rsi
  r13 : v.m.core.read .r13 = a0p
  guard : v.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  g : v.g = s.g
  env : MEnv E W b lb C fi sto ste sti v.m.memory

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`main` up to `0x27cb`**, for a program name without `/`. -/
theorem sha_main_spn {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hsr : ImpOk W sr (nm "strrchr") (strrchrStep E W)) (hpk : PrivKeep E)
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s u : PState}
    (hP : MainPro W b lb kb sr sc s u) (hal : (s.m.core.read .rsp).toNat % 16 = 8)
    (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (henv : MEnv E W b lb C fi sto ste sti u.m.memory)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    {a0p : Word} {a0 : List Byte}
    (hargv : loadN s.m.memory (s.m.core.read .rsi) 8 = some a0p)
    (hak : ∀ k, k < 8 → W.Kept ((s.m.core.read .rsi).toNat + k))
    (ha0 : CStr s.m.memory a0p a0) (ha0k : ∀ j, j < a0.length + 1 → W.Kept (a0p.toNat + j))
    (hnz : a0p ≠ 0#64) (hslash : ∀ x ∈ a0, x ≠ 0x2f#8)
    {g : Word} (hg : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j))
    (k : ∀ v, MainSpn E W b lb kb sr sc C fi sto ste sti s v g a0p → MustQ W Q v) : MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I hb hn
  have hB := hP.body
  have hroom := hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hMk := shaMemAll_keepI (lb := lb) (kb := kb) (sr := sr) (sc := sc) I hb
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a := by
    intro a ha
    by_contra hc
    exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  have hku : Keeps W.Kept s.m.memory u.m.memory := hB.keep.mono fun _ h => Or.inl h
  have hvk : ∀ x, VarR lb x → W.Kept x := fun x hx => by
    obtain ⟨h1, h2⟩ := hx
    have := henv.vars.kept (x - (lb + 0x2056a0#64).toNat) (by omega)
    rwa [show (lb + 0x2056a0#64).toNat + (x - (lb + 0x2056a0#64).toNat) = x by omega] at this
  -- argv[0] and the guard, as of `u`
  have hargvU : loadN u.m.memory (u.m.core.read .rsi) 8 = some a0p := by
    rw [hP.rsi, hku.loadN hak]; exact hargv
  have hgU : loadN u.m.memory (u.m.core.fsBase + BitVec.signExtend 64 0x28#32) 8 = some g := by
    rw [show BitVec.signExtend 64 0x28#32 = 0x28#64 by decide, hB.fs, hku.loadN hgk]; exact hg
  refine must_listed (o := 24) shaM_listing_ok.1 rfl hB.done (by rw [hP.rip]; exact hin _ (by decide))
    hB.mem.mn.mainA (by rw [hP.rip, ripadd]) ?_
  rw [exec_loadq _ _ _ _ _ _ hargvU, WP_ok]
  refine must_listed (o := 27) shaM_listing_ok.1 rfl hB.done (by simp only [hP.rip, ripadd]; exact hin _ (by decide))
    hB.mem.mn.mainA (by simp only [hP.rip, ripadd]) ?_
  rw [exec_loadfs _ _ _ _ _ _ (by exact hgU), WP_ok]
  -- an opaque state
  refine must_gen (fun v => v.m.core.rip = b + 0x2774#64 ∧ v.m.memory = u.m.memory ∧
      v.m.core.read .r13 = a0p ∧ v.m.core.read .rax = g ∧ v.m.core.fsBase = u.m.core.fsBase ∧ v.g = u.g ∧
      (∀ r, r ≠ .r13 → r ≠ .rax → v.m.core.read r = u.m.core.read r)) ?_ ?_
  · refine ⟨by simp [hP.rip, ripadd], rfl, by simp, by simp, rfl, rfl, fun r h1 h2 => by simp [h1, h2]⟩
  rintro v ⟨hrv, hmv, h13v, haxv, hfsv, hgv, hregv⟩
  have hbpv : v.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by rw [hregv _ (by decide) (by decide), hP.rbp]
  have hspv : v.m.core.read .rsp = u.m.core.read .rsp := hregv _ (by decide) (by decide)
  have hdv : v.g.done = none := by rw [hgv]; exact hB.done
  -- the guard into the frame
  have a1 : (v.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32).toNat = (s.m.core.read .rsp).toNat - 64 := by
    rw [hbpv, show BitVec.signExtend 64 0xffffffc8#32 = 0xffffffffffffffc8#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have pw1 : v.m.memory.Permitted .write (v.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32).toNat 8 := by
    rw [a1, hmv]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  refine must_listed (o := 36) shaM_listing_ok.1 rfl hdv (by rw [hrv]; exact hin _ (by decide))
    (by rw [hmv]; exact hB.mem.mn.mainA) (by rw [hrv, ripadd]) ?_
  rw [exec_storeq _ _ _ _ _ _ pw1, WP_ok]
  set A1 := v.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32 with hA1
  have hBv : Body W (ShaMemAll b lb kb sr sc) s v 328 4096 (sv6 s) :=
    hB.of_eq hmv hspv (by rw [hfsv]) (by rw [hgv])
  have hB1 : Body W (ShaMemAll b lb kb sr sc) s ⟨⟨v.m.core, storeMem v.m.memory A1 8 (v.m.core.read .rax)⟩, v.g⟩
      328 4096 (sv6 s) :=
    BodyX.store hMk hBv (by decide) (fun p hp => (sv6_bound328 s p hp).1) (by rw [a1]; omega) (by rw [a1]; omega)
      rfl rfl rfl rfl
  have henv1 : MEnv E W b lb C fi sto ste sti (storeMem v.m.memory A1 8 (v.m.core.read .rax)) := by
    rw [hmv]
    exact henv.store hpk fun x h1 h2 => by
      rw [a1] at h1 h2
      refine ⟨fun hp => ?_, fun hv => ?_⟩
      · have := E.S.priv_lo _ _ hp; omega
      · have := hKout x (hvk x hv)
        omega
  have hguard : (storeMem v.m.memory A1 8 (v.m.core.read .rax)).readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [g]) := by
    rw [← a1, ← haxv]
    exact storeMem_read8 (by rw [a1, hmv]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega))
  have hnz' : decide (a0p = 0#64) = false := by simp [hnz]
  refine must_listed (o := 40) shaM_listing_ok.1 rfl hdv (by simp only [hrv, ripadd]; exact hin _ (by decide))
    hB1.mem.mn.mainA (by simp only [hrv, ripadd]) ?_
  xstep [hrv]
  refine must_listed (o := 42) shaM_listing_ok.1 rfl hdv (hin _ (by decide)) hB1.mem.mn.mainA (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 45) shaM_listing_ok.1 rfl hdv (hin _ (by decide)) hB1.mem.mn.mainA (by rw [ripadd]) ?_
  xstep [eval_e_testQ, h13v, hnz']
  refine must_listed (o := 51) shaM_listing_ok.1 rfl hdv (hin _ (by decide)) hB1.mem.mn.mainA (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 54) shaM_listing_ok.1 rfl hdv (hin _ (by decide)) hB1.mem.mn.mainA (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 57) shaM_listing_ok.1 rfl hdv (hin _ (by decide)) hB1.mem.mn.mainA (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 60) shaM_listing_ok.1 rfl hdv (hin _ (by decide)) hB1.mem.mn.mainA (by rw [ripadd]) ?_
  xstep []
  -- at the call of `strrchr`, an opaque state
  set m1 := storeMem v.m.memory A1 8 (v.m.core.read .rax) with hm1
  refine must_gen (fun w => w.m.core.rip = b + 0x2791#64 ∧ w.m.memory = m1 ∧ w.g = v.g ∧
      w.m.core.read .rdi = a0p ∧ (w.m.core.read .rsi).setWidth 8 = 0x2f#8 ∧
      BitVec.setWidth 32 (w.m.core.read .r12) = BitVec.setWidth 32 (s.m.core.read .rdi) ∧
      w.m.core.read .rbx = s.m.core.read .rsi ∧ w.m.core.read .r13 = a0p ∧
      w.m.core.read .rbp = s.m.core.read .rsp - 8#64 ∧ w.m.core.read .rsp = u.m.core.read .rsp ∧
      w.m.core.fsBase = u.m.core.fsBase) ?_ ?_
  · refine ⟨by simp, rfl, rfl, by simp [h13v], by simp, ?_, ?_, by simp [h13v],
      by simp [hbpv], by simp [hspv], by simp [hfsv]⟩
    · simp [hregv _ (by decide : Reg.rdi ≠ .r13) (by decide), hP.rdi]
    · simp [hregv _ (by decide : Reg.rsi ≠ .r13) (by decide), hP.rsi]
  rintro w ⟨hrw, hmw, hgw, hdiw, hsiw, h12w, hbxw, h13w, hbpw, hspw, hfsw⟩
  have hBw : Body W (ShaMemAll b lb kb sr sc) s w 328 4096 (sv6 s) :=
    hB1.of_eq hmw (by rw [hspw]; exact hspv.symm) (by rw [hfsw]; exact hfsv.symm) (by rw [hgw])
  have hdw : w.g.done = none := by rw [hgw]; exact hdv
  have hwsp : (w.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 328 := by
    rw [hBw.rsp]; exact sub_toNat (by omega) (by omega)
  have hw8 : (w.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 336 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hwsp]; omega
  have hkw : Keeps W.Kept s.m.memory w.m.memory := hBw.keep.mono fun _ h => Or.inl h
  have hcw : CStr w.m.memory a0p a0 := cstr_keeps hkw ha0 ha0k
  have henvw : MEnv E W b lb C fi sto ste sti w.m.memory := by rw [hmw]; exact henv1
  have hpushK : ∀ a, (w.m.core.read .rsp - 8#64).toNat ≤ a → a < (w.m.core.read .rsp - 8#64).toNat + 8 →
      ¬ W.Kept a ∧ ¬ C a := by
    intro a h1 h2
    rw [hw8] at h1 h2
    exact ⟨(hroom.2.2 a (by omega) (by omega)).2.2, fun hc => by have := hC a hc; omega⟩
  have hal328 : ((s.m.core.read .rsp).toNat - 328) % 16 = 0 := by omega
  refine body_callK hMk hBw (by decide) (by decide) (sv6_bound328 s) hal328 hlz
    (o := 65) (so := 0x1b0) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaM_listing_ok.1 rfl (by rw [hrw]; exact hin _ (by decide)) (fun m h => h.mn.mainA)
    (by rw [hrw, BitVec.add_assoc]; rfl) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I hb (by decide)) (img_off I hb (by decide)) (fun m h => h.cl.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x1b0 + 4 + 6) + BitVec.signExtend 64 0x7936#32 = b + 0x9eb0#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.mn.strrchr)
    hsr.1 hsr.2.1 hsr.2.2.1 (fun r h => (impOk_fn hsr _ r).1 h)
    (fun he => ⟨he, a0, by
      rw [callEntry_mem, callEntry_read _ _ _ (by decide), hdiw]
      exact cstr_keeps (P := fun x => a0p.toNat ≤ x ∧ x < a0p.toNat + (a0.length + 1)) (pushMem_keeps fun x hx => by
        have := hKout x (ha0k (x - a0p.toNat) (by omega) |> fun h => by
          rwa [show a0p.toNat + (x - a0p.toNat) = x by omega] at h)
        rw [hw8]; omega) hcw (fun j hj => ⟨by omega, by omega⟩)⟩)
    (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, by rw [hv.2.1]; exact hdw⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro x hx hBx hrx hspx hcsx hkx
  obtain ⟨hlx, hgx, hox, hrx0⟩ := hx
  have henvx : MEnv E W b lb C fi sto ste sti x.m.memory :=
    MEnv.lib I (henvw.push (by rw [hw8]; omega) hpushK) hlx hox (fun a h => h.elim)
  have hcwe : CStr (callEntry w sr (b + 0x2750#64 + BitVec.ofNat 64 (65 + 5))).m.memory
      ((callEntry w sr (b + 0x2750#64 + BitVec.ofNat 64 (65 + 5))).m.core.read .rdi) a0 := by
    rw [callEntry_mem, callEntry_read _ _ _ (by decide), hdiw]
    exact cstr_keeps (P := fun x => a0p.toNat ≤ x ∧ x < a0p.toNat + (a0.length + 1)) (pushMem_keeps fun x hx => by
      have := hKout x (ha0k (x - a0p.toNat) (by omega) |> fun h => by
        rwa [show a0p.toNat + (x - a0p.toNat) = x by omega] at h)
      rw [hw8]; omega) hcw (fun j hj => ⟨by omega, by omega⟩)
  have hrax : x.m.core.read .rax = 0#64 := by
    have := hrx0 a0 hcwe
    rw [callEntry_read _ _ _ (by decide), hsiw] at this
    dsimp only at this
    rw [rfind_none hslash (by decide)] at this
    exact this
  have hdx : x.g.done = none := hBx.done
  have hgx' : x.g = s.g := by rw [hgx, callEntry_g, hgw, hgv, hP.g]
  refine must_listed (o := 70) shaM_listing_ok.1 rfl hdx (by rw [hrx]; exact img_off I hb (by decide))
    hBx.mem.mn.mainA (by rw [hrx]) ?_
  xstep [hrx]
  refine must_listed (o := 73) shaM_listing_ok.1 rfl hdx (hin _ (by decide)) hBx.mem.mn.mainA (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 76) shaM_listing_ok.1 rfl hdx (hin _ (by decide)) hBx.mem.mn.mainA (by rw [ripadd]) ?_
  xstep [eval_e_testQ, hrax]
  have hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, x.m.core.read r = w.m.core.read r := hcsx
  refine k _ ⟨hBx.of_eq rfl (by simp) rfl rfl, by simp, ?_, ?_, ?_, ?_, ?_, hgx', henvx⟩
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true, st_regs_apply]
    rw [hcs .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]), hbpw]
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true, st_regs_apply]
    rw [hcs .r12 (by simp [Silmaril.X86.sysv64_calleeSaved]), h12w]
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true, st_regs_apply]
    rw [hcs .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hbxw]
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true, st_regs_apply]
    rw [hcs .r13 (by simp [Silmaril.X86.sysv64_calleeSaved]), h13w]
  · rw [hkx.readBytes (fun j hj => ⟨Or.inr (by omega), fun h => h⟩), hmw]
    exact hguard

end Silmaril.Elf.Link.Dyn.Sha256sum
