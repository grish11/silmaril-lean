module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Mem
public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccRun

/-! # GNU `sha256sum`: from the kernel's entry state to `main`

The startup code of `sha256sum` is gcc's crt code, as in hello-gcc: `_start`
(`0x3a40`) calls `__libc_start_main` (the loose contract), which runs `_init` (`0x2000`) and
`frame_dummy` (`0x3b20`) and enters `main` (`0x2750`). `sha_reaches_main` proves that every
run reaches `main`'s entry, as a System V call returning to the library, with `argc`, `argv`,
`envp` and the image intact. What `main` does is the open goal `Task.shaMain`.
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
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

/-- The process world of `sha256sum` (executable at `b`, `libc.so.6` at `lb`):
`__libc_start_main` and `__cxa_finalize`, further imports `X` (address, kind), the contracts `N`
of named imports, and the argument area `A`. -/
def shaWorld (b lb gate : Word) (rel : Bool) (X : List (Word × Fn))
    (N : Name → PState → Silmaril.X86.RelIsa.Res PState → Prop) (A : Nat → Prop) : World where
  base := b
  size := 0xa188
  inits := [b + 0x2000#64, b + 0x3b20#64]
  finis := [b + 0x3ae0#64, b + 0x6d44#64]
  gate := gate
  lazy := none
  fns := [(lb + 0x2a200#64, .libcStartMain), (lb + 0x472c0#64, .cxaFinalize)] ++ X
  reliable := rel
  named := N
  args := A

variable {X : List (Word × Fn)} {N : Name → PState → Silmaril.X86.RelIsa.Res PState → Prop} {A : Nat → Prop}

theorem shaWorld_inImage (b lb gate : Word) (rel : Bool) :
    (shaWorld b lb gate rel X N A).InImage = ShaImg b := rfl

/-- The layout facts the loader guarantees. -/
structure ShaEnv (b lb gate : Word) : Prop where
  hb : b.toNat + 0xa188 < 2 ^ 64
  lsm_out : ¬ ShaImg b (lb + 0x2a200#64).toNat
  cxa_out : ¬ ShaImg b (lb + 0x472c0#64).toNat
  gate_out : ¬ ShaImg b gate.toNat
  gate_lsm : gate ≠ lb + 0x2a200#64
  gate_cxa : gate ≠ lb + 0x472c0#64

theorem sha_in {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {n : Nat} (hn : n < 0xa188) :
    ShaImg b (b + BitVec.ofNat 64 n).toNat := by
  rw [addr_toNat (by omega)]; simp only [ShaImg]; omega

theorem skeeps_push {b : Word} {W : World} (hW : W.InImage = ShaImg b) {m : Memory} {sp v : Word}
    (hroom : StackRoom W m sp) {sp' : Word} (hlo : sp.toNat - 4096 + 8 ≤ sp'.toNat)
    (hhi : sp'.toNat ≤ sp.toNat + 8) : Keeps (ShaImg b) m (pushMem m sp' v) := by
  apply pushMem_keeps
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hroom
  have h8 : (sp' - 8#64).toNat = sp'.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  rw [h8]
  by_contra hc
  have := (h3 (x) (by omega) (by omega)).2.2
  exact this (Or.inl (by rw [hW]; exact hx))

/-- A callback entered at `f` with the image facts. -/
structure SCb (W : World) (b lb : Word) (t : PState) (f : Word) : Prop where
  rip : t.m.core.rip = f
  al : (t.m.core.read .rsp).toNat % 16 = 8
  ret : t.m.memory.readBytes (t.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [W.gate])
  room : StackRoom W t.m.memory (t.m.core.read .rsp)
  mem : ShaMem b lb t.m.memory
  done : t.g.done = none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- (Any world whose image is `sha256sum`'s.) **`_start`** (`0x1080`): to `__libc_start_main` with `rdi = main`, `rsi = argc`,
`rdx = argv`, a System V entry and the image intact. -/
theorem sha_startW {b lb : Word} {W : World} (hW : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) {Q : PState → Prop}
    {s : PState} (hd : s.g.done = none) (hm : ShaMem b lb s.m.memory)
    (hrip : s.m.core.rip = b + 0x3a40#64) (hal : (s.m.core.read .rsp).toNat % 16 = 0)
    (hroom : StackRoom W s.m.memory (s.m.core.read .rsp)) {argc : Word}
    (hargc : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [argc]))
    (k : ∀ t : PState, t.g = s.g → t.m.core.rip = lb + 0x2a200#64 → ShaMem b lb t.m.memory →
      Keeps (ShaImg b) s.m.memory t.m.memory → AbiEntry t.m.core t.m.memory → t.m.core.read .rdi = b + 0x2750#64 →
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
  refine k _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using hm3
  · have hk : Keeps (ShaImg b) s.m.memory (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp)
        (s.m.core.read .rax)) (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64))
        (s.m.core.read .rsp - 8#64 - 8#64) (b + 0x3a65#64)) :=
      (skeeps_push (sp' := s.m.core.read .rsp) hW hroom (by omega) (by omega)).trans
        ((skeeps_push (sp' := s.m.core.read .rsp - 8#64) hW hroom.pushMem (by omega) (by omega)).trans
          (skeeps_push (sp' := s.m.core.read .rsp - 8#64 - 8#64) hW hroom.pushMem.pushMem (by omega) (by omega)))
    simpa using hk
  · refine abiEntry_of (v := b + 0x3a65#64) ?_ ?_
    · simp [e24]; omega
    · simpa using hret
  all_goals simp

theorem sha_start {b lb gate : Word} {rel : Bool} (E : ShaEnv b lb gate) {Q : PState → Prop}
    {s : PState} (hd : s.g.done = none) (hm : ShaMem b lb s.m.memory)
    (hrip : s.m.core.rip = b + 0x3a40#64) (hal : (s.m.core.read .rsp).toNat % 16 = 0)
    (hroom : StackRoom (shaWorld b lb gate rel X N A) s.m.memory (s.m.core.read .rsp)) {argc : Word}
    (hargc : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [argc]))
    (k : ∀ t : PState, t.g = s.g → t.m.core.rip = lb + 0x2a200#64 → ShaMem b lb t.m.memory →
      Keeps (ShaImg b) s.m.memory t.m.memory → AbiEntry t.m.core t.m.memory → t.m.core.read .rdi = b + 0x2750#64 →
      t.m.core.read .rsi = argc → t.m.core.read .rdx = s.m.core.read .rsp + 8#64 →
      MustQ (shaWorld b lb gate rel X N A) Q t) :
    MustQ (shaWorld b lb gate rel X N A) Q s :=
  sha_startW (shaWorld_inImage b lb gate rel) E.hb hd hm hrip hal hroom hargc k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- (Any world whose image is `sha256sum`'s.) **`_init`** (`0x1000`): `__gmon_start__` is 0, so it returns at once. -/
theorem sha_initW {b lb : Word} {W : World} (hW : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) {Q : PState → Prop}
    {t : PState} (hc : SCb W b lb t (b + 0x2000#64))
    (k : ∀ u : PState, u.m.core.rip = W.gate → u.g = t.g → u.m.memory = t.m.memory →
      MustQ W Q u) :
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
  exact k _ rfl rfl rfl

theorem sha_init {b lb gate : Word} {rel : Bool} (E : ShaEnv b lb gate) {Q : PState → Prop}
    {t : PState} (hc : SCb (shaWorld b lb gate rel X N A) b lb t (b + 0x2000#64))
    (k : ∀ u : PState, u.m.core.rip = gate → u.g = t.g → u.m.memory = t.m.memory →
      MustQ (shaWorld b lb gate rel X N A) Q u) :
    MustQ (shaWorld b lb gate rel X N A) Q t :=
  sha_initW (shaWorld_inImage b lb gate rel) E.hb hc k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- (Any world whose image is `sha256sum`'s.) **`frame_dummy`** (`0x1160`) and `register_tm_clones`: `__TMC_END__ - __TMC_END__ = 0`, so
it returns without calling `_ITM_registerTMCloneTable`. -/
theorem sha_frameDummyW {b lb : Word} {W : World} (hW : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) {Q : PState → Prop}
    {t : PState} (hc : SCb W b lb t (b + 0x3b20#64))
    (k : ∀ u : PState, u.m.core.rip = W.gate → u.g = t.g → u.m.memory = t.m.memory →
      MustQ W Q u) :
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
  exact k _ rfl rfl rfl

theorem sha_frameDummy {b lb gate : Word} {rel : Bool} (E : ShaEnv b lb gate) {Q : PState → Prop}
    {t : PState} (hc : SCb (shaWorld b lb gate rel X N A) b lb t (b + 0x3b20#64))
    (k : ∀ u : PState, u.m.core.rip = gate → u.g = t.g → u.m.memory = t.m.memory →
      MustQ (shaWorld b lb gate rel X N A) Q u) :
    MustQ (shaWorld b lb gate rel X N A) Q t :=
  sha_frameDummyW (shaWorld_inImage b lb gate rel) E.hb hc k

/-- The kernel's part of the initial state (System V process entry). -/
structure ShaStartState (W : World) (b : Word) (s : PState) (argc : Word) : Prop where
  rip : s.m.core.rip = b + 0x3a40#64
  al : (s.m.core.read .rsp).toNat % 16 = 0
  room : StackRoom W s.m.memory (s.m.core.read .rsp)
  argc : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [argc])
  ghost : s.g = { jobs := [], out := [], atexit := [], done := none }

theorem scb_of_enters {b lb gate : Word} {rel : Bool} (E : ShaEnv b lb gate) {s t : PState} {f : Word}
    (h : Enters (shaWorld b lb gate rel X N A) s t f) (hm : ShaMem b lb s.m.memory)
    (hd : t.g.done = none) : SCb (shaWorld b lb gate rel X N A) b lb t f :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hm.keep E.hb (by simpa [shaWorld_inImage] using keeps_img h.2.2.2.2.1), hd⟩

theorem skeepsImg {b lb gate : Word} {rel : Bool} {m m' : Memory}
    (h : Keeps (shaWorld b lb gate rel X N A).Kept m m') : Keeps (ShaImg b) m m' := by
  simpa [shaWorld_inImage] using keeps_img h

/-- The facts about a world that `sha256sum`'s start-up uses: its image, `__libc_start_main`
at `lb + 0x2a200`, the init and fini arrays, eager binding, and the gate outside the image. -/
structure ShaWorldOk (W : World) (b lb : Word) : Prop where
  img : W.InImage = ShaImg b
  hb : b.toNat + 0xa188 < 2 ^ 64
  lz : W.lazy = none
  inits : W.inits = [b + 0x2000#64, b + 0x3b20#64]
  finis : W.finis = [b + 0x3ae0#64, b + 0x6d44#64]
  lsm : W.fns.find? (·.1 == lb + 0x2a200#64) = some (lb + 0x2a200#64, .libcStartMain)
  lsm_out : ¬ ShaImg b (lb + 0x2a200#64).toNat
  gate_out : ¬ ShaImg b W.gate.toNat
  gate_lsm : W.gate ≠ lb + 0x2a200#64

theorem shaWorld_ok {b lb gate : Word} {rel : Bool} (E : ShaEnv b lb gate) :
    ShaWorldOk (shaWorld b lb gate rel X N A) b lb :=
  ⟨rfl, E.hb, rfl, rfl, rfl, by simp [shaWorld], E.lsm_out, E.gate_out, E.gate_lsm⟩

theorem scb_of_entersW {b lb : Word} {W : World} (hW : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {s t : PState} {f : Word} (h : Enters W s t f) (hm : ShaMem b lb s.m.memory)
    (hd : t.g.done = none) : SCb W b lb t f :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hm.keep hb (by rw [← hW]; exact keeps_img h.2.2.2.2.1), hd⟩

theorem skeepsImgW {b : Word} {W : World} (hW : W.InImage = ShaImg b) {m m' : Memory}
    (h : Keeps W.Kept m m') : Keeps (ShaImg b) m m' := by
  rw [← hW]; exact keeps_img h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- (Any world `W` with `sha256sum`'s image and start-up facts, `ShaWorldOk`.) **`sha256sum` reaches `main`**: from the kernel's entry state with the loaded image, every
run (with `__libc_start_main` as its loose contract) runs `_init` and `frame_dummy` and enters
`main` as a System V call returning to the library, with nothing written yet. -/
theorem sha_reaches_mainW {b lb : Word} {W : World} (E : ShaWorldOk W b lb) {Q : PState → Prop}
    {s : PState} {argc : Word} (hm : ShaMem b lb s.m.memory)
    (hs : ShaStartState W b s argc)
    (k : ∀ t, SCb W b lb t (b + 0x2750#64) → t.g.jobs = [.exitRax] →
      t.g.out = [] → t.g.atexit = [] → MustQ W Q t) :
    MustQ W Q s := by
  have hd0 : s.g.done = none := by rw [hs.ghost]
  have hgo : ¬ W.InImage W.gate.toNat := by
    rw [E.img]; exact E.gate_out
  refine sha_startW E.img E.hb hd0 hm hs.rip hs.al hs.room hs.argc ?_
  intro t1 hg1 hrip1 hm1 hk1 habi1 hrdi1 hrsi1 hrdx1
  have hd1 : t1.g.done = none := by rw [hg1]; exact hd0
  -- __libc_start_main
  refine must_fn hd1 (by rw [hrip1, E.img]; exact E.lsm_out)
    (by rw [hrip1]; exact Ne.symm E.gate_lsm) E.lz (f := .libcStartMain)
    (by rw [hrip1]; exact E.lsm) (fun r => Iff.rfl) habi1 ?_
  rintro t2 ⟨⟨hrip2, hk2, -⟩, hg2⟩
  have hm2 := hm1.keep E.hb (skeepsImgW E.img hk2)
  simp only [E.inits, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hrdi1] at hg2
  have hd2 : t2.g.done = none := by rw [hg2]; exact hd1
  -- _init
  refine gate_call hd2 (by rw [hrip2]; exact hgo) hrip2 (by rw [hg2]) ?_
  intro t3 he3 _ _ _ hg3
  have hd3 : t3.g.done = none := by rw [hg3]; exact hd2
  have hm3 := hm2.keep E.hb (skeepsImgW E.img he3.2.2.2.2.1)
  refine sha_initW E.img E.hb (scb_of_entersW E.img E.hb he3 hm2 hd3) ?_
  intro u3 hru3 hgu3 hmu3
  have hdu3 : u3.g.done = none := by rw [hgu3]; exact hd3
  -- frame_dummy
  refine gate_call hdu3 (by rw [hru3]; exact hgo) hru3 (by rw [hgu3, hg3]) ?_
  intro t4 he4 _ _ _ hg4
  have hd4 : t4.g.done = none := by rw [hg4]; exact hdu3
  have hm4 := (hmu3 ▸ hm3).keep E.hb (skeepsImgW E.img he4.2.2.2.2.1)
  refine sha_frameDummyW E.img E.hb (scb_of_entersW E.img E.hb he4 (hmu3 ▸ hm3) hd4) ?_
  intro u4 hru4 hgu4 hmu4
  have hdu4 : u4.g.done = none := by rw [hgu4]; exact hd4
  refine gate_main hdu4 (by rw [hru4]; exact hgo) hru4 (by rw [hgu4, hg4]) ?_
  intro t5 he5 _ _ _ hg5
  have hd5 : t5.g.done = none := by rw [hg5]; exact hdu4
  refine k t5 (scb_of_entersW E.img E.hb he5 (hmu4 ▸ hm4) hd5) (by rw [hg5]) ?_ ?_
  · rw [hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]
  · rw [hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]

/-- **`sha256sum` reaches `main`** (`sha_reaches_mainW` on `shaWorld`). -/
theorem sha_reaches_main {b lb gate : Word} {rel : Bool} (E : ShaEnv b lb gate) {Q : PState → Prop}
    {s : PState} {argc : Word} (hm : ShaMem b lb s.m.memory)
    (hs : ShaStartState (shaWorld b lb gate rel X N A) b s argc)
    (k : ∀ t, SCb (shaWorld b lb gate rel X N A) b lb t (b + 0x2750#64) → t.g.jobs = [.exitRax] →
      t.g.out = [] → t.g.atexit = [] → MustQ (shaWorld b lb gate rel X N A) Q t) :
    MustQ (shaWorld b lb gate rel X N A) Q s :=
  sha_reaches_mainW (shaWorld_ok E) hm hs k

theorem sha_not_lazy {Fs : List Blob} {bases : List Word} {ifn : Word → Option Word} {lazy : Bool}
    {res : Word} {mem : Memory} (h : ExeLoaded (shaFile :: Fs) bases ifn lazy res mem) :
    lazy = false := by
  obtain ⟨f, b', i, D, T, hf, -, hi, hlz, -⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf
  subst hf
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  cases lazy
  · rfl
  · exact absurd (hlz rfl) (by rw [sha_bindNow]; decide)

/-- **GNU `sha256sum`, from the loader relation to `main`**: for every `libcrypto.so.3`, `libc.so.6`
and `ld.so` agreeing with the chunks, every base, every ifunc choice and binding mode (only eager
is possible), every run reaches `main` as described by `sha_reaches_main`. -/
theorem sha256sum_reaches_main {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks)
    (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks) {b kb lb ldb res gate : Word}
    {ifn : Word → Option Word} {lazy rel : Bool} (E : ShaEnv b lb gate) {Q : PState → Prop}
    {s : PState} {argc : Word}
    (hload : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn lazy res s.m.memory)
    (hs : ShaStartState (shaWorld b lb gate rel X N A) b s argc)
    (k : ∀ t, SCb (shaWorld b lb gate rel X N A) b lb t (b + 0x2750#64) → t.g.jobs = [.exitRax] →
      t.g.out = [] → t.g.atexit = [] → MustQ (shaWorld b lb gate rel X N A) Q t) :
    MustQ (shaWorld b lb gate rel X N A) Q s := by
  have := sha_not_lazy hload
  subst this
  exact sha_reaches_main E (shaMem_of_loaded hk hc hl hload) hs k

end Silmaril.Elf.Link.Dyn.Sha256sum
