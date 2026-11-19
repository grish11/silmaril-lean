module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinLoaded
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Run

/-! # GNU `sha256sum`, stdin tier: a weaker library hypothesis at `main`, and why it is needed

**Finding** (`sha_stdin_no_progress`): the hypothesis of `StdinLoaded.sha256sum_stdin` on the
world's guarantee at `main`'s entry,

  `hA : ∀ t, W.atMain t → ∃ C fi a0p g, MainLib E W b lb C fi t a0p a0 data g`,

makes **every** such world stuck somewhere: `MainLib` fixes `argc = 1` (and `argv`, the guard,
libc's `stdin` variable, all in kept memory), while `World.atMain` is the library's promise for
*every* `.main` job, whatever its registers and the kept memory. At a `.main` job with `argc = 0`
the gate step has no outcome. So `proc W` never has global `Progress`, the route of Hello's
non-vacuity (`proc_progress` + `Must.exists_run`) is closed, and `hA` itself is trivially met by
`atMain := fun t => ∃ …, MainLib …` — it says nothing about whether a run exists.

**Weakening** (`sha256sum_stdinK`): `hA` is only asked at the `main` entries that the start-up
can produce from the kernel's state `s`: those whose kept memory (image, argument area, TCB) is
`s`'s, with `s`'s `fsBase`, `rsi = argv = rsp₀ + 8`, and `rdi` the zero-extended low half of the
kernel's `argc`. The start-up establishes these (`sha_startK`, `sha_reaches_mainK`: every
library step and callback entry keeps `W.Kept` and `fsBase`; `_start` writes only its stack page,
which `StackRoom` puts outside `W.Kept`; `_init` and `frame_dummy` write nothing). A world can then
meet `hA'` with an `atMain` that is *conditional* on these facts, so that `main` can be entered
from every state (global progress) — the kept part of `MainLib` comes from the kernel's state.
`sha256sum_stdin` follows from `sha256sum_stdinK` (`sha256sum_stdin_of_K`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

/-- **No world meeting `sha256sum_stdin`'s `hA` has global progress**: it is stuck at the gate
before a `main (0, 0, 0)` job. -/
theorem sha_stdin_no_progress {E : Env} {W : World} {b lb : Word} {a0 data : List Byte}
    (hA : ∀ t, W.atMain t → ∃ C fi a0p g, MainLib E W b lb C fi t a0p a0 data g)
    (hgate : ¬ W.InImage W.gate.toNat) : ¬ Silmaril.X86.RelIsa.Progress (proc W) :=
  not_progress_main (P := fun t => BitVec.setWidth 32 (t.m.core.read .rdi) = 1#32)
    (fun t h => (hA t h).elim fun _ h => h.elim fun _ h => h.elim fun _ h => h.elim fun _ h => h.argc)
    hgate (f := 0) (a1 := 0) (a2 := 0) (a3 := 0) fun t h1 _ _ h => by rw [h1] at h; exact absurd h (by decide)

/-- A push inside the stack page keeps `W.Kept` (`StackRoom` puts the page outside it). -/
theorem skeeps_pushK {W : World} {m : Memory} {sp v : Word}
    (hroom : StackRoom W m sp) {sp' : Word} (hlo : sp.toNat - 4096 + 8 ≤ sp'.toNat)
    (hhi : sp'.toNat ≤ sp.toNat + 8) : Keeps W.Kept m (pushMem m sp' v) := by
  apply pushMem_keeps
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hroom
  have h8 : (sp' - 8#64).toNat = sp'.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  rw [h8]
  by_contra hc
  exact (h3 x (by omega) (by omega)).2.2 hx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `sha_startW` keeping all of `W.Kept` (not only the image) and `fsBase`. -/
theorem sha_startK {b lb : Word} {W : World} (hW : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) {Q : PState → Prop}
    {s : PState} (hd : s.g.done = none) (hm : ShaMem b lb s.m.memory)
    (hrip : s.m.core.rip = b + 0x3a40#64) (hal : (s.m.core.read .rsp).toNat % 16 = 0)
    (hroom : StackRoom W s.m.memory (s.m.core.read .rsp)) {argc : Word}
    (hargc : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [argc]))
    (k : ∀ t : PState, t.g = s.g → t.m.core.rip = lb + 0x2a200#64 → ShaMem b lb t.m.memory →
      Keeps W.Kept s.m.memory t.m.memory → t.m.core.fsBase = s.m.core.fsBase →
      AbiEntry t.m.core t.m.memory → t.m.core.read .rdi = b + 0x2750#64 →
      t.m.core.read .rsi = argc → t.m.core.read .rdx = s.m.core.read .rsp + 8#64 →
      MustQ W Q t) :
    MustQ W Q s := by
  have hl := hm.crt
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => by rw [hW]; exact sha_in hb hn
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have e24 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 24 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e16]; omega
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have hm1 : ShaMem b lb (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax)) :=
    hm.keep hb (skeeps_push hW hroom (by omega) (by omega))
  have p2 : (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax)).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inr rfl) (by omega) (by omega)
  have hm2 : ShaMem b lb (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)) :=
    hm1.keep hb (skeeps_push hW hroom.pushMem (by omega) (by omega))
  have p3 : (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem.pushMem (Or.inr rfl) (by omega) (by omega)
  have r3 : (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)).Permitted .read
      (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem.pushMem (Or.inl rfl) (by omega) (by omega)
  have hm3 : ShaMem b lb (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp)
      (s.m.core.read .rax)) (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64))
      (s.m.core.read .rsp - 8#64 - 8#64) (b + 0x3a65#64)) :=
    hm2.keep hb (skeeps_push hW hroom.pushMem.pushMem (by omega) (by omega))
  have hret := pushMem_read (v := b + 0x3a65#64) r3 p3
  refine must_listed (o := 0x0) sha_listing_ok.2.1 rfl hd (by rw [hrip]; exact hin _ (by decide)) hl
    (by rw [hrip]; exact (BitVec.add_zero _).symm) ?_
  xstep [hrip]
  refine must_listed (o := 0x4) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x6) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x9) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hargc]
  refine must_listed (o := 0xa) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xd) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  simp only [and16 hal (by omega)]
  refine must_listed (o := 0x11) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  refine must_listed (o := 0x12) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hm1.crt (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p2)]
  xstep []
  refine must_listed (o := 0x13) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hm2.crt (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x16) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hm2.crt (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x18) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hm2.crt (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x1f) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hm2.crt (by rw [ripadd]) ?_
  xstep []
  rw [pushWord_mem (by simpa using p3)]
  simp only [hm2.lsm, WP_ok, st_write_regs, st_read_mk]
  refine k _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using hm3
  · have hk : Keeps W.Kept s.m.memory (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp)
        (s.m.core.read .rax)) (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64))
        (s.m.core.read .rsp - 8#64 - 8#64) (b + 0x3a65#64)) :=
      (skeeps_pushK (sp' := s.m.core.read .rsp) hroom (by omega) (by omega)).trans
        ((skeeps_pushK (sp' := s.m.core.read .rsp - 8#64) hroom.pushMem (by omega) (by omega)).trans
          (skeeps_pushK (sp' := s.m.core.read .rsp - 8#64 - 8#64) hroom.pushMem.pushMem (by omega) (by omega)))
    simpa using hk
  · rfl
  · refine abiEntry_of (v := b + 0x3a65#64) ?_ ?_
    · simp [e24]; omega
    · simpa using hret
  all_goals simp


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `sha_initW` keeping `fsBase`. -/
theorem sha_initK {b lb : Word} {W : World} (hW : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) {Q : PState → Prop}
    {t : PState} (hc : SCb W b lb t (b + 0x2000#64))
    (k : ∀ u : PState, u.m.core.rip = W.gate → u.g = t.g → u.m.memory = t.m.memory →
      u.m.core.fsBase = t.m.core.fsBase → MustQ W Q u) :
    MustQ W Q t := by
  have hl := hc.mem.init
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => by rw [hW]; exact sha_in hb hn
  have hd := hc.done
  refine must_listed (o := 0) sha_listing_ok.1 rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip]; exact (BitVec.add_zero _).symm) ?_
  xstep [hc.rip]
  refine must_listed (o := 4) sha_listing_ok.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 8) sha_listing_ok.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [hc.mem.gmon]
  refine must_listed (o := 0xf) sha_listing_ok.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x12) sha_listing_ok.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.BlockCert9.eval_e_test]
  refine must_listed (o := 0x16) sha_listing_ok.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x1a) sha_listing_ok.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hc.ret]
  exact k _ rfl rfl rfl rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `sha_frameDummyW` keeping `fsBase`. -/
theorem sha_frameDummyK {b lb : Word} {W : World} (hW : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) {Q : PState → Prop}
    {t : PState} (hc : SCb W b lb t (b + 0x3b20#64))
    (k : ∀ u : PState, u.m.core.rip = W.gate → u.g = t.g → u.m.memory = t.m.memory →
      u.m.core.fsBase = t.m.core.fsBase → MustQ W Q u) :
    MustQ W Q t := by
  have hl := hc.mem.crt
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => by rw [hW]; exact sha_in hb hn
  have hd := hc.done
  refine must_listed (o := 0xe0) sha_listing_ok.2.1 rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip, ripadd]) ?_
  xstep [hc.rip]
  refine must_listed (o := 0xe4) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x60) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x67) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x6e) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x71) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x74) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x78) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x7c) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x7f) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x82) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  have hz : Silmaril.X86.Ext.Cond.eval
      (Silmaril.X86.Ext.ShiftOp.sar.flags
        (Silmaril.X86.Ext.ShiftOp.shr.result (0#64) 63 + Silmaril.X86.Ext.ShiftOp.sar.result (0#64) 3) 1
        (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.add (Silmaril.X86.Ext.ShiftOp.shr.result (0#64) 63)
          (Silmaril.X86.Ext.ShiftOp.sar.result (0#64) 3))) Silmaril.X86.Ext.Cond.e = some true := by
    decide
  xstep [hz]
  refine must_listed (o := 0x98) sha_listing_ok.2.1 rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hc.ret]
  exact k _ rfl rfl rfl rfl


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`sha256sum` reaches `main`** (`sha_reaches_mainA`) with what the start-up guarantees of
`main`'s entry beyond the image: the kept memory and `fsBase` of the kernel's state, `argv`
(`rsi = rsp₀ + 8`) and `argc` (`rdi`, the zero-extended low half of the kernel's `argc`). -/
theorem sha_reaches_mainK {b lb : Word} {W : World} (E : ShaWorldOk W b lb) {Q : PState → Prop}
    {s : PState} {argc : Word} (hm : ShaMem b lb s.m.memory)
    (hs : ShaStartState W b s argc)
    (k : ∀ t, SCb W b lb t (b + 0x2750#64) → t.g.jobs = [.exitRax] →
      t.g.out = [] → t.g.atexit = [] → Keeps W.Kept s.m.memory t.m.memory →
      t.m.core.fsBase = s.m.core.fsBase → t.m.core.read .rsi = s.m.core.read .rsp + 8#64 →
      t.m.core.read .rdi = (argc.setWidth 32).setWidth 64 →
      (t.g.allocs = 0 ∧ t.g.heap = 0 ∧ t.g.files = 0) → W.atMain t → MustQ W Q t) :
    MustQ W Q s := by
  have hd0 : s.g.done = none := by rw [hs.ghost]
  have hgo : ¬ W.InImage W.gate.toNat := by
    rw [E.img]; exact E.gate_out
  refine sha_startK E.img E.hb hd0 hm hs.rip hs.al hs.room hs.argc ?_
  intro t1 hg1 hrip1 hm1 hk1 hfs1 habi1 hrdi1 hrsi1 hrdx1
  have hd1 : t1.g.done = none := by rw [hg1]; exact hd0
  -- __libc_start_main
  refine must_fn hd1 (by rw [hrip1, E.img]; exact E.lsm_out)
    (by rw [hrip1]; exact Ne.symm E.gate_lsm) E.lz (f := .libcStartMain)
    (by rw [hrip1]; exact E.lsm) (fun r => Iff.rfl) habi1 ?_
  rintro t2 ⟨⟨hrip2, hk2, hfs2⟩, hg2⟩
  have hm2 := hm1.keep E.hb (skeepsImgW E.img hk2)
  simp only [E.inits, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hrdi1, hrsi1,
    hrdx1] at hg2
  have hd2 : t2.g.done = none := by rw [hg2]; exact hd1
  -- _init
  refine gate_call hd2 (by rw [hrip2]; exact hgo) hrip2 (by rw [hg2]) ?_
  intro t3 he3 _ _ _ hg3
  have hd3 : t3.g.done = none := by rw [hg3]; exact hd2
  have hm3 := hm2.keep E.hb (skeepsImgW E.img he3.2.2.2.2.1)
  refine sha_initK E.img E.hb (scb_of_entersW E.img E.hb he3 hm2 hd3) ?_
  intro u3 hru3 hgu3 hmu3 hfu3
  have hdu3 : u3.g.done = none := by rw [hgu3]; exact hd3
  -- frame_dummy
  refine gate_call hdu3 (by rw [hru3]; exact hgo) hru3 (by rw [hgu3, hg3]) ?_
  intro t4 he4 _ _ _ hg4
  have hd4 : t4.g.done = none := by rw [hg4]; exact hdu3
  have hm4 := (hmu3 ▸ hm3).keep E.hb (skeepsImgW E.img he4.2.2.2.2.1)
  refine sha_frameDummyK E.img E.hb (scb_of_entersW E.img E.hb he4 (hmu3 ▸ hm3) hd4) ?_
  intro u4 hru4 hgu4 hmu4 hfu4
  have hdu4 : u4.g.done = none := by rw [hgu4]; exact hd4
  refine gate_main' hdu4 (by rw [hru4]; exact hgo) hru4 (by rw [hgu4, hg4]) ?_
  intro t5 he5 h5di h5si _ hg5 hat5
  have hd5 : t5.g.done = none := by rw [hg5]; exact hdu4
  have hK : Keeps W.Kept s.m.memory t5.m.memory :=
    (((hk1.trans hk2).trans he3.2.2.2.2.1).trans (hmu3 ▸ he4.2.2.2.2.1)).trans (hmu4 ▸ he5.2.2.2.2.1)
  refine k t5 (scb_of_entersW E.img E.hb he5 (hmu4 ▸ hm4) hd5) (by rw [hg5]) ?_ ?_ hK ?_ ?_ ?_ ?_ hat5
  · rw [hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]
  · rw [hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]
  · rw [he5.2.2.2.2.2, hfu4, he4.2.2.2.2.2, hfu3, he3.2.2.2.2.2, hfs2, hfs1]
  · rw [h5si]
  · rw [h5di]
  · rw [hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]; exact ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **GNU `sha256sum`, stdin tier, from the loader relation to the specification**, with the
weaker library hypothesis: `hA` is asked only at `main` entries with the kernel's kept memory,
`fsBase`, `argv` and `argc` (see the module doc). -/
theorem sha256sum_stdinK {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res sr sc : Word} {ifn : Word → Option Word} {lazy : Bool}
    (hsr : ifn (lb + 0xb5210#64) = some sr) (hsc : ifn (lb + 0xb4410#64) = some sc)
    {E : Env} {R : ShaRep} {W : World} (I : MainImps E W b lb sr) (T : TailImps E R W b lb kb sc)
    (XO : ExitOk E W b lb) {s : PState} {argc : Word}
    (hload : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn lazy res s.m.memory)
    (hs : ShaStartState W b s argc)
    (hR : 1 ≤ E.maxAllocs ∧ 0x8048 ≤ E.maxHeap) {a0 data : List Byte}
    (hA : ∀ t, W.atMain t → Keeps W.Kept s.m.memory t.m.memory → t.m.core.fsBase = s.m.core.fsBase →
      t.m.core.read .rsi = s.m.core.read .rsp + 8#64 → t.m.core.read .rdi = (argc.setWidth 32).setWidth 64 →
      ∃ C fi a0p g, MainLib E W b lb C fi t a0p a0 data g) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) :
    MustQ W (Ended (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).status fun w =>
      w = (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).stdout.map UInt8.toBitVec ∧
      (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).stderr = []) s := by
  have := sha_not_lazy hload
  subst this
  have hb := XO.wo.hb
  refine sha_reaches_mainK XO.wo (shaMem_of_loaded hk hc hl hload) hs ?_
  intro t hC hj ho ha hKK hfs hrsi hrdi hcnt hat
  have hK : Keeps (ShaImg b) s.m.memory t.m.memory := skeepsImgW XO.wo.img hKK
  obtain ⟨C, fi, a0p, g, L⟩ := hA t hat hKK hfs hrsi hrdi
  obtain ⟨hclr, hbss, hbssw⟩ := shaTailMem_of_loaded hk hc hl hload
  have hrw0 := shaRw_of_loaded hload
  have hI : ∀ n, n < 0xa188 → ∀ j, j < 8 → n + j < 0xa188 → ShaImg b ((b + BitVec.ofNat 64 n).toNat + j) :=
    fun n hn j hj hnj => by rw [addr_toNat (by omega)]; exact ⟨by omega, by omega⟩
  refine sha_main_stdin_spec_ok I T XO (C := C) (fi := fi) (a0p := a0p) (g := g)
    ⟨hC.rip, Silmaril.Elf.Link.Dyn.Hello.abiEntry_of hC.al hC.ret, hC.room, ⟨hC.done, ha, ho, hj⟩,
      (shaMemAll_of_loaded hk hc hl hsr hsc hload).keep hb hK, fun j hj => ?_, L.lo, L.env, L.hC, L.pinC,
      L.pinK, L.optC, L.optK, L.optL, L.opt, L.lbB, L.imgVar, L.argsImg, L.argc, L.argv, L.argv0, L.argv0k,
      L.a0s, L.a0k, L.a0nz, L.noSlash, L.guard, L.guardk, by rw [hcnt.1, hcnt.2.1]; omega⟩
    ⟨hC.ret, hC.al, L.lo, (shaMainAll_of_loaded hk hc hl hload).keepW hb (imgW_img hK),
      by rw [loadN_keeps hK (fun j hj => hI 0x9f68 (by decide) j hj (by omega))]; exact hclr,
      by rw [loadN_keeps hK (fun j hj => hI 0xa040 (by decide) j (by omega) (by omega))]; exact hbss,
      (hK.permitted (fun j hj => hI 0xa040 (by decide) j (by omega) (by omega))).2 hbssw,
      L.var, L.vark, L.varImg, L.fi0, L.fiO, L.fiE, L.guard, L.guardk, L.guardImg, L.imgVar, L.argsImg, L.optK,
      L.avHi, L.av, L.avA, L.avR, L.avW, L.avVar, L.avIn, L.avG⟩ posix fs
  have hj' : ShaImg b (b.toNat + 0xa160 + j) := ⟨by omega, by omega⟩
  rw [(hK _ hj').2, (hK _ hj').2]
  exact hrw0 j hj

/-- The original statement follows (its `hA` ignores the extra facts). -/
theorem sha256sum_stdin_of_K {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res sr sc : Word} {ifn : Word → Option Word} {lazy : Bool}
    (hsr : ifn (lb + 0xb5210#64) = some sr) (hsc : ifn (lb + 0xb4410#64) = some sc)
    {E : Env} {R : ShaRep} {W : World} (I : MainImps E W b lb sr) (T : TailImps E R W b lb kb sc)
    (XO : ExitOk E W b lb) {s : PState} {argc : Word}
    (hload : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn lazy res s.m.memory)
    (hs : ShaStartState W b s argc)
    (hR : 1 ≤ E.maxAllocs ∧ 0x8048 ≤ E.maxHeap) {a0 data : List Byte}
    (hA : ∀ t, W.atMain t → ∃ C fi a0p g, MainLib E W b lb C fi t a0p a0 data g) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) :
    MustQ W (Ended (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).status fun w =>
      w = (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).stdout.map UInt8.toBitVec ∧
      (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).stderr = []) s :=
  sha256sum_stdinK hk hc hl hsr hsc I T XO hload hs hR (fun t h _ _ _ _ => hA t h) posix fs


end Silmaril.Elf.Link.Dyn.Sha256sum
