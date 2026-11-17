module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.PrintPutc

/-! # sha256sum's output path, part (a): the three inline `putc`s of a result line

Each from `main`'s code to the next instruction after it, by the fast path (store into
`stdout`'s buffer, `putc_fast`) or the slow path (`__overflow (stdout, c)`):
* `sha_putSpace1` (`0x2bf8` → `0x2c1b`): `' '`;
* `sha_putMark` (`0x2c1b` → `0x2c52`): `binary > 0 ? '*' : ' '`, here `' '` (`binary` is `0` or `-1`);
* `sha_putDelim` (`0x2c60` → `0x2c8a`): the line delimiter (the byte at `rbp - 0xec`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams

theorem eval_ae_sub (x y : BitVec 64) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .ae = some (decide (y.toNat ≤ x.toNat)) := by
  simp only [Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot, Option.map_some]
  rw [Silmaril.X86.Ext.subBorrowN_eq (w := 63) x y]
  by_cases h : y.toNat ≤ x.toNat
  · simp [BitVec.ult, h]
  · simp [BitVec.ult, h]; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sha_putSpace1 {E : Env} {W : World} {b lb sc : Word} (I : PrintImps E W b lb sc) (hP : PutcLaw E) (hD : StreamsDisj E)
    {Q : PState → Prop} {s0 u : PState} {fr n sv : Nat} {saved : List (Nat × Word)}
    (hB : Body W (ShaMemP b lb sc) s0 u fr n saved) (hrip : u.m.core.rip = b + 0x2bf8#64)
    (hv : StdVars E W lb u.m.memory)
    (hfk : ∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a)
    (hlo : E.S.lo + n ≤ (s0.m.core.read .rsp).toNat) (hfw : E.stdoutF.toNat + 0x38 < 2 ^ 64)
    (hfr : fr + 8 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s0.m.core.read .rsp).toNat - fr) % 16 = 0) (hrel : W.reliable = true)
    {st : St} (hst : StdoutIs E u.m.memory st)
    (k : ∀ v st', Body W (ShaMemP b lb sc) s0 v fr n saved → v.m.core.rip = b + 0x2c1b#64 →
      v.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) →
      StdoutIs E v.m.memory st' → st'.err = st.err → st'.rd = st.rd → st'.eof = st.eof → st'.reading = st.reading →
      v.g.out ++ st'.buf = u.g.out ++ st.buf ++ [0x20#8] →
      v.g.jobs = u.g.jobs → v.g.atexit = u.g.atexit → v.g.done = none →
      (v.g.inp = u.g.inp ∧ v.g.allocs = u.g.allocs ∧ v.g.heap = u.g.heap ∧
        v.g.files = u.g.files) → v.g.err = u.g.err →
      Keeps (fun a => W.Kept a ∨ (u.m.core.read .rsp).toNat ≤ a) u.m.memory v.m.memory →
      (∀ f st'', f ≠ E.stdoutF → E.S.file u.m.memory f st'' → E.S.file v.m.memory f st'') →
      LibK E W u.m.memory v.m.memory → MustQ W Q v) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hd := hB.done
  obtain ⟨⟨p, hp⟩, ⟨e, he⟩, -⟩ := E.S.ptrs _ _ _ hst.1
  refine must_listed (o := 110) shaP_listing_ok.1 rfl hd (by rw [hrip]; exact hin _ (by decide))
    hB.mem.printLine (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  xstep [hrip, hB.mem.stdoutV]
  refine must_listed (o := 117) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_loadq .rdi .rax _ _ _ E.stdoutF (by simpa using hv.out)]
  simp only [WP_ok, ripadd]
  refine must_listed (o := 120) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_loadqd .rax .rdi 0x28#32 _ _ _ p (by simpa using hp)]
  simp only [WP_ok, ripadd]
  refine must_listed (o := 124) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_cmpq_rdi _ _ _ 48#32 e ?hc]
  case hc => simpa using he
  simp only [WP_ok, ripadd]
  refine must_listed (o := 128) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.flagsN, eval_ae_sub]
  have hfoot := fun a (ha : E.S.foot u.m.memory E.stdoutF a) => E.S.foot_lo _ _ _ _ hst.1 ha
  have hnk := fun a (ha : E.S.foot u.m.memory E.stdoutF a) => hfk _ _ a hst.1 ha
  have hu : (u.m.core.read .rsp).toNat = (s0.m.core.read .rsp).toNat - fr := by
    rw [hB.rsp]; exact sub_toNat (by have := hB.room.1; omega) (by have := hB.room.1; omega)
  by_cases hlt : p.toNat < e.toNat
  · -- the fast path
    rw [show decide (e.toNat ≤ p.toNat) = false by simp; omega]
    simp only [WP_ok]
    obtain ⟨-, hpw, hww, -⟩ := E.S.putc _ _ _ p e 0#8 hst.1 hp he hlt
    obtain ⟨hpr, hdis⟩ := hP.1 _ _ _ p e hst.1 hp he hlt
    obtain ⟨m1, hs1, hS1⟩ := Silmaril.X86.Ext.storeN_isSome (v := p + 1#64) hww
    have hpw1 : m1.Permitted .write p.toNat 1 := by
      unfold Memory.Permitted at hpw ⊢; rw [Silmaril.X86.Memory.checkSpan_congr hS1.frame.1]; exact hpw
    obtain ⟨m2, hs2, -⟩ := Silmaril.X86.Ext.storeN_isSome (v := (0x20#8).setWidth 64) hpw1
    obtain ⟨hf2, hk2, hreg⟩ := putc_fast hst.1 hp he hlt hdis hpr hfw hs1 hs2
    have hf28 : (E.stdoutF + 0x28#64).toNat = E.stdoutF.toNat + 0x28 := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]; rfl
    have hku1 : Keeps (fun a => W.Kept a ∨ E.S.lo ≤ a) u.m.memory m1 :=
      keeps_of_writesOnly hS1.frame fun x hx => by
        simp only [Silmaril.X86.Ext.leBytes, List.length_ofFn]
        by_contra hc
        have hft := (E.S.ptrs _ _ _ hst.1).2.2 x (by omega) (by omega)
        rcases hx with h | h
        · exact hnk x hft h
        · have := hfoot x hft; omega
    have hm1 := shaMemP_keep I.img I.hb _ _ hB.mem (hku1.mono fun a ha => Or.inl (Or.inl ha))
    refine must_listed (o := 134) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
      (by rw [ripadd]) ?_
    xstep []
    refine must_listed (o := 138) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
      (by rw [ripadd]) ?_
    rw [exec_storeq_rdi _ _ m1 _ 40#32 ?hs]
    case hs => simpa using hs1
    simp only [WP_ok, ripadd]
    refine must_listed (o := 142) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hm1.printLine
      (by rw [ripadd]) ?_
    rw [exec_storeb_imm _ _ m2 _ 0x20#8 ?hs]
    case hs => simpa using hs2
    simp only [WP_ok, ripadd]
    -- what the two stores kept
    have hku : Keeps (fun a => W.Kept a ∨ E.S.lo ≤ a) u.m.memory m2 :=
      hk2.mono fun a ha hf => by
        rcases ha with h | h
        · exact hnk a hf h
        · have := hfoot a hf; omega
    have hperm : ∀ a acc, m2.permits acc a = u.m.memory.permits acc a := fun a acc => by
      unfold Memory.permits; rw [hreg]
    have hc8 : ((0x20#8).setWidth 64 : Word).setWidth 8 = 0x20#8 := by decide
    rw [hc8] at hf2
    refine k _ { st with buf := st.buf ++ [0x20#8] } ⟨?_, ?_, ?_, ?_, ?_, hd, ?_, ?_⟩ ?_ ?_ ?_
      ⟨hf2, hst.2⟩ rfl rfl rfl rfl (by simp) rfl rfl hd ⟨rfl, rfl, rfl, rfl⟩ rfl (hku.mono fun a ha => ?_)
      (fun f st'' hne hf => (E.S.local_ _ _ _ _ (hk2.mono fun a ha hfa => hD _ _ _ _ _ a hne hf hst.1 ha hfa) hf).1)
      (LibK.putc hP (LibK.refl E W _) hst.1 hk2 hreg)
    · simpa using hB.rsp
    · exact keepF (hB.keep.trans (hku.mono fun a ha => by
        rcases ha with h | h
        · exact Or.inl h
        · right; omega))
    · exact hB.room.keeps fun a _ _ acc => hperm a acc
    · exact shaMemP_keep I.img I.hb _ _ hB.mem (hku.mono fun a ha => Or.inl (Or.inl ha))
    · simpa using hB.fs
    · intro q hq
      rw [hku.readBytes (fun j hj => Or.inr (by have := (hsv q hq).1; have := (hsv q hq).2; omega))]
      exact hB.saved q hq
    · intro a h1 h2 acc; rw [hperm]; exact hB.perm a h1 h2 acc
    · rfl
    · simp
    · intro r hr
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rcases ha with h | h
      · exact Or.inl h
      · right; have := hB.room.1; omega
  · -- the slow path: `__overflow (stdout, ' ')`
    rw [show decide (e.toNat ≤ p.toNat) = true by simp; omega]
    simp only [WP_ok]
    refine must_listed (o := 46) shaP_listing_ok.2.2.1 rfl hd (hin _ (by decide)) hB.mem.slowPut
      (by rw [ripadd]) ?_
    xstep []
    have hlo8 : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat := by
      rw [sub_toNat (k := 8) (by have := hB.room.1; omega) (by decide), hu]; omega
    refine body_call (shaMemP_keep I.img I.hb) (hB.of_eq rfl (by simp) rfl rfl) hfr hn hsv hal I.lz
      (o := 51) (so := 0x240) (pb := b + 0x23c0#64) (fp := fun _ => False)
      shaP_listing_ok.2.2.1 rfl (hin _ (by decide)) (fun m h => h.slowPut) (by simp)
      shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
      (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
      (fun m h => by
        rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x240 + 4 + 6) + BitVec.signExtend 64 0x78ee#32 =
          b + 0x9ef8#64 by simp only [BitVec.add_assoc]; rfl]
        exact h.overflow)
      I.overflow.1 I.overflow.2.1 I.overflow.2.2.1 (fun r h => (impOk_fn I.overflow _ r).1 h)
      (fun habi => ⟨habi, by rw [callEntry_read _ _ _ (by decide)]; simp, st, by
        rw [callEntry_mem]; exact ⟨file_push hst.1 (by simpa using hlo8), hst.2⟩⟩)
      (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, hv.2.1.2.2.1⟩)
      (fun x h => h.elim) (fun x h => h.elim) ?_
    intro v hv hB2 hrip2 hrsp2 hcs2
    have hLv : LibK E W u.m.memory v.m.memory := by
      refine LibK.call0 ?_ ?_ hv.1
      · exact LibK.refl E W _
      · simpa using hlo8
    obtain ⟨⟨⟨-, hkv⟩, -⟩, ⟨hj, ha, hdn, hi, hie, hal, hhp, hfi⟩, hoth, happ⟩ := hv
    obtain ⟨st', hst', heof, hrd, hrdg, hor⟩ := happ st (by rw [callEntry_mem]; exact ⟨file_push hst.1 (by simpa using hlo8), hst.2⟩)
    obtain ⟨hout, herr⟩ : v.g.out ++ st'.buf = u.g.out ++ st.buf ++ [0x20#8] ∧ st'.err = st.err := by
      rcases hor with h | ⟨hr, -⟩
      · refine ⟨?_, h.2⟩
        rw [h.1]; simp [callEntry]
      · rw [hrel] at hr; cases hr
    refine must_listed (o := 56) shaP_listing_ok.2.2.1 rfl hdn (by rw [hrip2, ripadd]; exact hin _ (by decide))
      hB2.mem.slowPut (by rw [hrip2, ripadd]) ?_
    xstep [hrip2]
    have hroom1 := hB.room.1
    have hu8 : 8 ≤ (u.m.core.read .rsp).toNat := by rw [hu]; omega
    refine k _ st' (hB2.of_eq rfl (by simp) rfl rfl) (by simp) (by simpa using hrsp2) (fun r hr => ?_)
      hst' herr hrd heof hrdg (by simpa using hout) (by simpa using hj) (by simpa using ha) hdn ⟨by simpa using hi, by simpa using hal, by simpa using hhp, by simpa using hfi⟩ (by simpa using hie) ?_
      (fun f st'' hne hf => hoth f st'' (by simpa using hne) (by rw [callEntry_mem]; exact file_push hf (by simpa using hlo8))) hLv
    · have : r ≠ .rsp := fun h => Silmaril.X86.sysv64_rsp_not_calleeSaved (h ▸ hr)
      simp only [Silmaril.X86.State.read_mk_regs] 
      rw [hcs2 r hr]
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · refine (pushMem_keeps fun x hx => ?_).trans (hkv.mono fun x hx => ⟨?_, id⟩)
      · rcases hx with h | h
        · by_cases hc : (s0.m.core.read .rsp).toNat - n ≤ x ∧ x < (s0.m.core.read .rsp).toNat + 8
          · exact absurd h (hB.room.2.2 x hc.1 hc.2).2.2
          · simp; omega
        · simp; omega
      · rcases hx with h | h
        · exact Or.inl h
        · right; simp; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sha_putMark {E : Env} {W : World} {b lb sc : Word} (I : PrintImps E W b lb sc) (hP : PutcLaw E) (hD : StreamsDisj E)
    {Q : PState → Prop} {s0 u : PState} {fr n sv : Nat} {saved : List (Nat × Word)}
    (hB : Body W (ShaMemP b lb sc) s0 u fr n saved) (hrip : u.m.core.rip = b + 0x2c1b#64)
    {bv : Word} (hbin : loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32) 4 = some bv)
    (hbv : bv.setWidth 32 = 0#32 ∨ bv.setWidth 32 = 0xffffffff#32)
    (hv : StdVars E W lb u.m.memory)
    (hfk : ∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a)
    (hlo : E.S.lo + n ≤ (s0.m.core.read .rsp).toNat) (hfw : E.stdoutF.toNat + 0x38 < 2 ^ 64)
    (hfr : fr + 8 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s0.m.core.read .rsp).toNat - fr) % 16 = 0) (hrel : W.reliable = true)
    {st : St} (hst : StdoutIs E u.m.memory st)
    (k : ∀ v st', Body W (ShaMemP b lb sc) s0 v fr n saved → v.m.core.rip = b + 0x2c52#64 →
      v.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) →
      StdoutIs E v.m.memory st' → st'.err = st.err → st'.rd = st.rd → st'.eof = st.eof → st'.reading = st.reading →
      v.g.out ++ st'.buf = u.g.out ++ st.buf ++ [0x20#8] →
      v.g.jobs = u.g.jobs → v.g.atexit = u.g.atexit → v.g.done = none →
      (v.g.inp = u.g.inp ∧ v.g.allocs = u.g.allocs ∧ v.g.heap = u.g.heap ∧
        v.g.files = u.g.files) → v.g.err = u.g.err →
      Keeps (fun a => W.Kept a ∨ (u.m.core.read .rsp).toNat ≤ a) u.m.memory v.m.memory →
      (∀ f st'', f ≠ E.stdoutF → E.S.file u.m.memory f st'' → E.S.file v.m.memory f st'') →
      LibK E W u.m.memory v.m.memory → MustQ W Q v) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hd := hB.done
  obtain ⟨⟨p, hp⟩, ⟨e, he⟩, -⟩ := E.S.ptrs _ _ _ hst.1
  -- `binary > 0 ? '*' : ' '` with `binary ≤ 0`
  refine must_listed (o := 145) shaP_listing_ok.1 rfl hd (by rw [hrip]; exact hin _ (by decide))
    hB.mem.printLine (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  xstep [hrip]
  refine must_listed (o := 150) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_cmpd0_rbp _ _ _ 0xffffff38#32 bv ?hc0]
  case hc0 => simpa using hbin
  simp only [WP_ok, ripadd]
  have hg : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp (bv.setWidth 32) 0#32)
      .g = some false := by rcases hbv with h | h <;> rw [h] <;> decide
  refine must_listed (o := 157) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 162) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep [hg, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Sz.write]
  refine must_listed (o := 165) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep [hB.mem.stdoutV]
  refine must_listed (o := 172) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_loadq .rdi .rax _ _ _ E.stdoutF (by simpa using hv.out)]
  simp only [WP_ok, ripadd]
  refine must_listed (o := 175) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_loadqd .rax .rdi 0x28#32 _ _ _ p (by simpa using hp)]
  simp only [WP_ok, ripadd]
  refine must_listed (o := 179) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_cmpq_rdi _ _ _ 48#32 e ?hc]
  case hc => simpa using he
  simp only [WP_ok, ripadd]
  refine must_listed (o := 183) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.flagsN, eval_ae_sub]
  have hfoot := fun a (ha : E.S.foot u.m.memory E.stdoutF a) => E.S.foot_lo _ _ _ _ hst.1 ha
  have hnk := fun a (ha : E.S.foot u.m.memory E.stdoutF a) => hfk _ _ a hst.1 ha
  have hu : (u.m.core.read .rsp).toNat = (s0.m.core.read .rsp).toNat - fr := by
    rw [hB.rsp]; exact sub_toNat (by have := hB.room.1; omega) (by have := hB.room.1; omega)
  by_cases hlt : p.toNat < e.toNat
  · -- the fast path
    rw [show decide (e.toNat ≤ p.toNat) = false by simp; omega]
    simp only [WP_ok]
    obtain ⟨-, hpw, hww, -⟩ := E.S.putc _ _ _ p e 0#8 hst.1 hp he hlt
    obtain ⟨hpr, hdis⟩ := hP.1 _ _ _ p e hst.1 hp he hlt
    obtain ⟨m1, hs1, hS1⟩ := Silmaril.X86.Ext.storeN_isSome (v := p + 1#64) hww
    have hpw1 : m1.Permitted .write p.toNat 1 := by
      unfold Memory.Permitted at hpw ⊢; rw [Silmaril.X86.Memory.checkSpan_congr hS1.frame.1]; exact hpw
    obtain ⟨m2, hs2, -⟩ := Silmaril.X86.Ext.storeN_isSome (v := (0x20#8).setWidth 64) hpw1
    obtain ⟨hf2, hk2, hreg⟩ := putc_fast hst.1 hp he hlt hdis hpr hfw hs1 hs2
    have hf28 : (E.stdoutF + 0x28#64).toNat = E.stdoutF.toNat + 0x28 := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]; rfl
    have hku1 : Keeps (fun a => W.Kept a ∨ E.S.lo ≤ a) u.m.memory m1 :=
      keeps_of_writesOnly hS1.frame fun x hx => by
        simp only [Silmaril.X86.Ext.leBytes, List.length_ofFn]
        by_contra hc
        have hft := (E.S.ptrs _ _ _ hst.1).2.2 x (by omega) (by omega)
        rcases hx with h | h
        · exact hnk x hft h
        · have := hfoot x hft; omega
    have hm1 := shaMemP_keep I.img I.hb _ _ hB.mem (hku1.mono fun a ha => Or.inl (Or.inl ha))
    refine must_listed (o := 189) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
      (by rw [ripadd]) ?_
    xstep []
    refine must_listed (o := 193) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
      (by rw [ripadd]) ?_
    rw [exec_storeq_rdi _ _ m1 _ 40#32 ?hs]
    case hs => simpa using hs1
    simp only [WP_ok, ripadd]
    refine must_listed (o := 197) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hm1.printLine
      (by rw [ripadd]) ?_
    rw [exec_storeb_reg .rsi _ _ m2 _ ?hs]
    case hs => simpa using hs2
    simp only [WP_ok, ripadd]
    -- what the two stores kept
    have hku : Keeps (fun a => W.Kept a ∨ E.S.lo ≤ a) u.m.memory m2 :=
      hk2.mono fun a ha hf => by
        rcases ha with h | h
        · exact hnk a hf h
        · have := hfoot a hf; omega
    have hperm : ∀ a acc, m2.permits acc a = u.m.memory.permits acc a := fun a acc => by
      unfold Memory.permits; rw [hreg]
    have hc8 : ((0x20#8).setWidth 64 : Word).setWidth 8 = 0x20#8 := by decide
    rw [hc8] at hf2
    refine k _ { st with buf := st.buf ++ [0x20#8] } ⟨?_, ?_, ?_, ?_, ?_, hd, ?_, ?_⟩ ?_ ?_ ?_
      ⟨hf2, hst.2⟩ rfl rfl rfl rfl (by simp) rfl rfl hd ⟨rfl, rfl, rfl, rfl⟩ rfl (hku.mono fun a ha => ?_)
      (fun f st'' hne hf => (E.S.local_ _ _ _ _ (hk2.mono fun a ha hfa => hD _ _ _ _ _ a hne hf hst.1 ha hfa) hf).1)
      (LibK.putc hP (LibK.refl E W _) hst.1 hk2 hreg)
    · simpa using hB.rsp
    · exact keepF (hB.keep.trans (hku.mono fun a ha => by
        rcases ha with h | h
        · exact Or.inl h
        · right; omega))
    · exact hB.room.keeps fun a _ _ acc => hperm a acc
    · exact shaMemP_keep I.img I.hb _ _ hB.mem (hku.mono fun a ha => Or.inl (Or.inl ha))
    · simpa using hB.fs
    · intro q hq
      rw [hku.readBytes (fun j hj => Or.inr (by have := (hsv q hq).1; have := (hsv q hq).2; omega))]
      exact hB.saved q hq
    · intro a h1 h2 acc; rw [hperm]; exact hB.perm a h1 h2 acc
    · rfl
    · simp
    · intro r hr
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rcases ha with h | h
      · exact Or.inl h
      · right; have := hB.room.1; omega
  · -- the slow path: `__overflow (stdout, ' ')`
    rw [show decide (e.toNat ≤ p.toNat) = true by simp; omega]
    simp only [WP_ok]
    have hlo8 : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat := by
      rw [sub_toNat (k := 8) (by have := hB.room.1; omega) (by decide), hu]; omega
    refine body_call (shaMemP_keep I.img I.hb) (hB.of_eq rfl (by simp) rfl rfl) hfr hn hsv hal I.lz
      (o := 61) (so := 0x240) (pb := b + 0x23c0#64) (fp := fun _ => False)
      shaP_listing_ok.2.2.1 rfl (hin _ (by decide)) (fun m h => h.slowPut) (by simp)
      shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
      (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
      (fun m h => by
        rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x240 + 4 + 6) + BitVec.signExtend 64 0x78ee#32 =
          b + 0x9ef8#64 by simp only [BitVec.add_assoc]; rfl]
        exact h.overflow)
      I.overflow.1 I.overflow.2.1 I.overflow.2.2.1 (fun r h => (impOk_fn I.overflow _ r).1 h)
      (fun habi => ⟨habi, by rw [callEntry_read _ _ _ (by decide)]; simp, st, by
        rw [callEntry_mem]; exact ⟨file_push hst.1 (by simpa using hlo8), hst.2⟩⟩)
      (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, hv.2.1.2.2.1⟩)
      (fun x h => h.elim) (fun x h => h.elim) ?_
    intro v hv hB2 hrip2 hrsp2 hcs2
    have hLv : LibK E W u.m.memory v.m.memory := by
      refine LibK.call0 ?_ ?_ hv.1
      · exact LibK.refl E W _
      · simpa using hlo8
    obtain ⟨⟨⟨-, hkv⟩, -⟩, ⟨hj, ha, hdn, hi, hie, hal, hhp, hfi⟩, hoth, happ⟩ := hv
    obtain ⟨st', hst', heof, hrd, hrdg, hor⟩ := happ st (by rw [callEntry_mem]; exact ⟨file_push hst.1 (by simpa using hlo8), hst.2⟩)
    obtain ⟨hout, herr⟩ : v.g.out ++ st'.buf = u.g.out ++ st.buf ++ [0x20#8] ∧ st'.err = st.err := by
      rcases hor with h | ⟨hr, -⟩
      · refine ⟨?_, h.2⟩
        rw [h.1]; simp [callEntry]
      · rw [hrel] at hr; cases hr
    refine must_listed (o := 66) shaP_listing_ok.2.2.1 rfl hdn (by rw [hrip2, ripadd]; exact hin _ (by decide))
      hB2.mem.slowPut (by rw [hrip2, ripadd]) ?_
    xstep [hrip2]
    have hroom1 := hB.room.1
    have hu8 : 8 ≤ (u.m.core.read .rsp).toNat := by rw [hu]; omega
    refine k _ st' (hB2.of_eq rfl (by simp) rfl rfl) (by simp) (by simpa using hrsp2) (fun r hr => ?_)
      hst' herr hrd heof hrdg (by simpa using hout) (by simpa using hj) (by simpa using ha) hdn ⟨by simpa using hi, by simpa using hal, by simpa using hhp, by simpa using hfi⟩ (by simpa using hie) ?_
      (fun f st'' hne hf => hoth f st'' (by simpa using hne) (by rw [callEntry_mem]; exact file_push hf (by simpa using hlo8))) hLv
    · have : r ≠ .rsp := fun h => Silmaril.X86.sysv64_rsp_not_calleeSaved (h ▸ hr)
      simp only [Silmaril.X86.State.read_mk_regs] 
      rw [hcs2 r hr]
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · refine (pushMem_keeps fun x hx => ?_).trans (hkv.mono fun x hx => ⟨?_, id⟩)
      · rcases hx with h | h
        · by_cases hc : (s0.m.core.read .rsp).toNat - n ≤ x ∧ x < (s0.m.core.read .rsp).toNat + 8
          · exact absurd h (hB.room.2.2 x hc.1 hc.2).2.2
          · simp; omega
        · simp; omega
      · rcases hx with h | h
        · exact Or.inl h
        · right; simp; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sha_putDelim {E : Env} {W : World} {b lb sc : Word} (I : PrintImps E W b lb sc) (hP : PutcLaw E) (hD : StreamsDisj E)
    {Q : PState → Prop} {s0 u : PState} {fr n sv : Nat} {saved : List (Nat × Word)}
    (hB : Body W (ShaMemP b lb sc) s0 u fr n saved) (hrip : u.m.core.rip = b + 0x2c60#64)
    {dl : Word} (hdl : loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff14#32) 1 = some dl)
    (hdlo : E.S.lo ≤ (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff14#32).toNat)
    (hv : StdVars E W lb u.m.memory)
    (hfk : ∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a)
    (hlo : E.S.lo + n ≤ (s0.m.core.read .rsp).toNat) (hfw : E.stdoutF.toNat + 0x38 < 2 ^ 64)
    (hfr : fr + 8 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s0.m.core.read .rsp).toNat - fr) % 16 = 0) (hrel : W.reliable = true)
    {st : St} (hst : StdoutIs E u.m.memory st)
    (k : ∀ v st', Body W (ShaMemP b lb sc) s0 v fr n saved → v.m.core.rip = b + 0x2c8a#64 →
      v.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) →
      StdoutIs E v.m.memory st' → st'.err = st.err → st'.rd = st.rd → st'.eof = st.eof → st'.reading = st.reading →
      v.g.out ++ st'.buf = u.g.out ++ st.buf ++ [dl.setWidth 8] →
      v.g.jobs = u.g.jobs → v.g.atexit = u.g.atexit → v.g.done = none →
      (v.g.inp = u.g.inp ∧ v.g.allocs = u.g.allocs ∧ v.g.heap = u.g.heap ∧
        v.g.files = u.g.files) → v.g.err = u.g.err →
      Keeps (fun a => W.Kept a ∨ (u.m.core.read .rsp).toNat ≤ a) u.m.memory v.m.memory →
      (∀ f st'', f ≠ E.stdoutF → E.S.file u.m.memory f st'' → E.S.file v.m.memory f st'') →
      LibK E W u.m.memory v.m.memory → MustQ W Q v) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hd := hB.done
  obtain ⟨⟨p, hp⟩, ⟨e, he⟩, -⟩ := E.S.ptrs _ _ _ hst.1
  refine must_listed (o := 214) shaP_listing_ok.1 rfl hd (by rw [hrip]; exact hin _ (by decide))
    hB.mem.printLine (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  xstep [hrip, hB.mem.stdoutV]
  refine must_listed (o := 221) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_loadq .rdi .rax _ _ _ E.stdoutF (by simpa using hv.out)]
  simp only [WP_ok, ripadd]
  refine must_listed (o := 224) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_loadqd .rax .rdi 0x28#32 _ _ _ p (by simpa using hp)]
  simp only [WP_ok, ripadd]
  refine must_listed (o := 228) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_cmpq_rdi _ _ _ 48#32 e ?hc]
  case hc => simpa using he
  simp only [WP_ok, ripadd]
  refine must_listed (o := 232) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.flagsN, eval_ae_sub]
  have hfoot := fun a (ha : E.S.foot u.m.memory E.stdoutF a) => E.S.foot_lo _ _ _ _ hst.1 ha
  have hnk := fun a (ha : E.S.foot u.m.memory E.stdoutF a) => hfk _ _ a hst.1 ha
  have hu : (u.m.core.read .rsp).toNat = (s0.m.core.read .rsp).toNat - fr := by
    rw [hB.rsp]; exact sub_toNat (by have := hB.room.1; omega) (by have := hB.room.1; omega)
  by_cases hlt : p.toNat < e.toNat
  · -- the fast path
    rw [show decide (e.toNat ≤ p.toNat) = false by simp; omega]
    simp only [WP_ok]
    obtain ⟨-, hpw, hww, -⟩ := E.S.putc _ _ _ p e 0#8 hst.1 hp he hlt
    obtain ⟨hpr, hdis⟩ := hP.1 _ _ _ p e hst.1 hp he hlt
    obtain ⟨m1, hs1, hS1⟩ := Silmaril.X86.Ext.storeN_isSome (v := p + 1#64) hww
    have hpw1 : m1.Permitted .write p.toNat 1 := by
      unfold Memory.Permitted at hpw ⊢; rw [Silmaril.X86.Memory.checkSpan_congr hS1.frame.1]; exact hpw
    obtain ⟨m2, hs2, -⟩ := Silmaril.X86.Ext.storeN_isSome (v := (dl.setWidth 8).setWidth 64) hpw1
    obtain ⟨hf2, hk2, hreg⟩ := putc_fast hst.1 hp he hlt hdis hpr hfw hs1 hs2
    have hf28 : (E.stdoutF + 0x28#64).toNat = E.stdoutF.toNat + 0x28 := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]; rfl
    have hku1 : Keeps (fun a => W.Kept a ∨ E.S.lo ≤ a) u.m.memory m1 :=
      keeps_of_writesOnly hS1.frame fun x hx => by
        simp only [Silmaril.X86.Ext.leBytes, List.length_ofFn]
        by_contra hc
        have hft := (E.S.ptrs _ _ _ hst.1).2.2 x (by omega) (by omega)
        rcases hx with h | h
        · exact hnk x hft h
        · have := hfoot x hft; omega
    have hm1 := shaMemP_keep I.img I.hb _ _ hB.mem (hku1.mono fun a ha => Or.inl (Or.inl ha))
    refine must_listed (o := 238) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
      (by rw [ripadd]) ?_
    xstep []
    refine must_listed (o := 242) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
      (by rw [ripadd]) ?_
    rw [exec_storeq_rdi _ _ m1 _ 40#32 ?hs]
    case hs => simpa using hs1
    simp only [WP_ok, ripadd]
    refine must_listed (o := 246) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hm1.printLine
      (by rw [ripadd]) ?_
    rw [exec_movzb_rbp .rdi _ _ _ 0xffffff14#32 dl ?hl]
    case hl =>
      have := loadN_keeps (n := 1) hku1 (a := u.m.core.read .rbp + BitVec.signExtend 64 0xffffff14#32)
        (fun i hi => Or.inr (by omega))
      refine Eq.trans ?_ (this.trans hdl)
      congr 2
    simp only [WP_ok, ripadd]
    refine must_listed (o := 253) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hm1.printLine
      (by rw [ripadd]) ?_
    rw [exec_storeb_reg .rdi _ _ m2 _ ?hs]
    case hs => simpa using hs2
    simp only [WP_ok, ripadd]
    -- what the two stores kept
    have hku : Keeps (fun a => W.Kept a ∨ E.S.lo ≤ a) u.m.memory m2 :=
      hk2.mono fun a ha hf => by
        rcases ha with h | h
        · exact hnk a hf h
        · have := hfoot a hf; omega
    have hperm : ∀ a acc, m2.permits acc a = u.m.memory.permits acc a := fun a acc => by
      unfold Memory.permits; rw [hreg]
    have hc8 : ((dl.setWidth 8).setWidth 64 : Word).setWidth 8 = dl.setWidth 8 := by simp
    rw [hc8] at hf2
    refine k _ { st with buf := st.buf ++ [dl.setWidth 8] } ⟨?_, ?_, ?_, ?_, ?_, hd, ?_, ?_⟩ ?_ ?_ ?_
      ⟨hf2, hst.2⟩ rfl rfl rfl rfl (by simp) rfl rfl hd ⟨rfl, rfl, rfl, rfl⟩ rfl (hku.mono fun a ha => ?_)
      (fun f st'' hne hf => (E.S.local_ _ _ _ _ (hk2.mono fun a ha hfa => hD _ _ _ _ _ a hne hf hst.1 ha hfa) hf).1)
      (LibK.putc hP (LibK.refl E W _) hst.1 hk2 hreg)
    · simpa using hB.rsp
    · exact keepF (hB.keep.trans (hku.mono fun a ha => by
        rcases ha with h | h
        · exact Or.inl h
        · right; omega))
    · exact hB.room.keeps fun a _ _ acc => hperm a acc
    · exact shaMemP_keep I.img I.hb _ _ hB.mem (hku.mono fun a ha => Or.inl (Or.inl ha))
    · simpa using hB.fs
    · intro q hq
      rw [hku.readBytes (fun j hj => Or.inr (by have := (hsv q hq).1; have := (hsv q hq).2; omega))]
      exact hB.saved q hq
    · intro a h1 h2 acc; rw [hperm]; exact hB.perm a h1 h2 acc
    · rfl
    · simp
    · intro r hr
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rcases ha with h | h
      · exact Or.inl h
      · right; have := hB.room.1; omega
  · -- the slow path: `__overflow (stdout, delim)`
    rw [show decide (e.toNat ≤ p.toNat) = true by simp; omega]
    simp only [WP_ok]
    refine must_listed (o := 0) shaP_listing_ok.2.2.1 rfl hd (hin _ (by decide)) hB.mem.slowPut
      (by simp) ?_
    rw [exec_movzb_rbp .rsi _ _ _ 0xffffff14#32 dl ?hl]
    case hl => simpa using hdl
    simp only [WP_ok, ripadd]
    have hlo8 : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat := by
      rw [sub_toNat (k := 8) (by have := hB.room.1; omega) (by decide), hu]; omega
    refine body_call (shaMemP_keep I.img I.hb) (hB.of_eq rfl (by simp) rfl rfl) hfr hn hsv hal I.lz
      (o := 7) (so := 0x240) (pb := b + 0x23c0#64) (fp := fun _ => False)
      shaP_listing_ok.2.2.1 rfl (hin _ (by decide)) (fun m h => h.slowPut) (by simp)
      shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
      (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
      (fun m h => by
        rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x240 + 4 + 6) + BitVec.signExtend 64 0x78ee#32 =
          b + 0x9ef8#64 by simp only [BitVec.add_assoc]; rfl]
        exact h.overflow)
      I.overflow.1 I.overflow.2.1 I.overflow.2.2.1 (fun r h => (impOk_fn I.overflow _ r).1 h)
      (fun habi => ⟨habi, by rw [callEntry_read _ _ _ (by decide)]; simp, st, by
        rw [callEntry_mem]; exact ⟨file_push hst.1 (by simpa using hlo8), hst.2⟩⟩)
      (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, hv.2.1.2.2.1⟩)
      (fun x h => h.elim) (fun x h => h.elim) ?_
    intro v hv hB2 hrip2 hrsp2 hcs2
    have hLv : LibK E W u.m.memory v.m.memory := by
      refine LibK.call0 ?_ ?_ hv.1
      · exact LibK.refl E W _
      · simpa using hlo8
    obtain ⟨⟨⟨-, hkv⟩, -⟩, ⟨hj, ha, hdn, hi, hie, hal, hhp, hfi⟩, hoth, happ⟩ := hv
    obtain ⟨st', hst', heof, hrd, hrdg, hor⟩ := happ st (by rw [callEntry_mem]; exact ⟨file_push hst.1 (by simpa using hlo8), hst.2⟩)
    obtain ⟨hout, herr⟩ : v.g.out ++ st'.buf = u.g.out ++ st.buf ++ [dl.setWidth 8] ∧ st'.err = st.err := by
      rcases hor with h | ⟨hr, -⟩
      · refine ⟨?_, h.2⟩
        rw [h.1]; simp [callEntry]
      · rw [hrel] at hr; cases hr
    refine must_listed (o := 12) shaP_listing_ok.2.2.1 rfl hdn (by rw [hrip2, ripadd]; exact hin _ (by decide))
      hB2.mem.slowPut (by rw [hrip2, ripadd]) ?_
    xstep [hrip2]
    have hroom1 := hB.room.1
    have hu8 : 8 ≤ (u.m.core.read .rsp).toNat := by rw [hu]; omega
    refine k _ st' (hB2.of_eq rfl (by simp) rfl rfl) (by simp) (by simpa using hrsp2) (fun r hr => ?_)
      hst' herr hrd heof hrdg (by simpa using hout) (by simpa using hj) (by simpa using ha) hdn ⟨by simpa using hi, by simpa using hal, by simpa using hhp, by simpa using hfi⟩ (by simpa using hie) ?_
      (fun f st'' hne hf => hoth f st'' (by simpa using hne) (by rw [callEntry_mem]; exact file_push hf (by simpa using hlo8))) hLv
    · have : r ≠ .rsp := fun h => Silmaril.X86.sysv64_rsp_not_calleeSaved (h ▸ hr)
      simp only [Silmaril.X86.State.read_mk_regs] 
      rw [hcs2 r hr]
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · refine (pushMem_keeps fun x hx => ?_).trans (hkv.mono fun x hx => ⟨?_, id⟩)
      · rcases hx with h | h
        · by_cases hc : (s0.m.core.read .rsp).toNat - n ≤ x ∧ x < (s0.m.core.read .rsp).toNat + 8
          · exact absurd h (hB.room.2.2 x hc.1 hc.2).2.2
          · simp; omega
        · simp; omega
      · rcases hx with h | h
        · exact Or.inl h
        · right; simp; omega

end Silmaril.Elf.Link.Dyn.Sha256sum
