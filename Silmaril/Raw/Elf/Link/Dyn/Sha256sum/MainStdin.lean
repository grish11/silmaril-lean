module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinTasks
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainHead
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Start
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Close
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CertMem

/-! # GNU `sha256sum`, stdin tier: `main` from its entry to the end of the process

`sha_main_stdin`: from `main`'s entry with no operand (`argc = 1`) and standard input holding
`data`, every run ends with status 0 having written `stdinLine data` (which is the
specification's record, `stdinLine_spec`). Proved from `main`'s entry to `0x29fd` (`sha_main_head`,
`sha_main_buf`, `sha_main_getopt`); the rest is stated as two goals, both proved downstream
(`StdinMain.task_mainStdinTail`, `ExitPath.task_exitPath`; the composition without goals is
`StdinMain.sha_main_stdin_ok` / `sha_main_stdin_spec_ok`):

* `Task.mainStdinTail`: `0x29fd` to `main`'s return (the operand `"-"`, `digest_file`
  (`Task.digestStdin`), the result line (`Task.printLine`), `rpl_fclose (stdin)`, the epilogue);
* `Task.exitPath`: from `main`'s return with status 0 to the end of the process (`exit`,
  `close_stdout`, the destructors with `__cxa_finalize`, `_fini`).
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

/-- The imports `main`'s start-up calls, with their contracts, in the world `W`. -/
structure MainImps (E : Env) (W : World) (b lb sr : Word) : Prop where
  lz : W.lazy = none
  img : W.InImage = ShaImg b
  hb : b.toNat + 0xa188 < 2 ^ 64
  strrchr : ImpOk W sr (nm "strrchr") (strrchrStep E W)
  loc : LocImps E W lb
  atexit : ImpOk W (lb + 0x471f0#64) (nm "__cxa_atexit") (framed E W (fun _ _ => False) (cxaAtexitFirst W))
  setvbuf : ImpOk W (lb + 0x88630#64) (nm "setvbuf") (setvbufStep E W)
  getopt : ImpOk W (lb + 0xf5ad0#64) (nm "getopt_long") (getoptNoneStep E W)

/-- A fresh output stream on descriptor `fd`. -/
def outSt (fd : Nat) : St := ⟨fd, false, [], false, false, false, []⟩

/-- **`main`'s entry on the stdin tier**: the System V entry, the image, the library state
(`stdout`, `stderr`, `stdin` holding `data`), `argv = [a0]` with `a0` free of `/`, and the layout. -/
structure MainEntryS (E : Env) (W : World) (b lb kb sr sc : Word) (C : Nat → Prop) (fi : Word)
    (s : PState) (a0p : Word) (a0 data : List Byte) (g : Word) : Prop where
  rip : s.m.core.rip = b + 0x2750#64
  abi : AbiEntry s.m.core s.m.memory
  room : Room W s.m.memory (s.m.core.read .rsp) 4096
  ghost : s.g.done = none ∧ s.g.atexit = [] ∧ s.g.out = [] ∧ s.g.jobs = [.exitRax]
  mem : ShaMemAll b lb kb sr sc s.m.memory
  rw : ShaRw b s.m.memory
  lo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat
  env : MEnv E W b lb C fi (outSt 1) (outSt 2) (stdinSt data) s.m.memory
  hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a
  pinC : ∀ a, PinR lb a → C a
  pinK : ∀ a, PinR lb a → ¬ W.Kept a
  optC : ∀ a, OptR E a → C a
  optK : ∀ a, OptR E a → ¬ W.Kept a
  optL : ∀ a, OptR E a → a + 48 < (s.m.core.read .rsp).toNat
  opt : E.optindA.toNat + 4 < 2 ^ 64
  lbB : lb.toNat + 0x2056b0 < 2 ^ 64
  imgVar : ∀ a, ShaImg b a → ¬ VarR lb a
  argsImg : ∀ a, W.args a → ¬ ShaImg b a
  argc : BitVec.setWidth 32 (s.m.core.read .rdi) = 1#32
  argv : ∀ m, Keeps W.args s.m.memory m → Argv m (s.m.core.read .rsi) [a0]
  argv0 : loadN s.m.memory (s.m.core.read .rsi) 8 = some a0p
  argv0k : ∀ k, k < 8 → W.Kept ((s.m.core.read .rsi).toNat + k)
  a0s : CStr s.m.memory a0p a0
  a0k : ∀ j, j < a0.length + 1 → W.Kept (a0p.toNat + j)
  a0nz : a0p ≠ 0#64
  noSlash : ∀ x ∈ a0, x ≠ 0x2f#8
  guard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j)
  /-- the library's resources for the buffer's `malloc` -/
  res : s.g.allocs < E.maxAllocs ∧ s.g.heap + 0x8048 ≤ E.maxHeap

/-- `main` has returned to the library with status 0, `stdout` holding `X` in total. -/
structure MainRet (E : Env) (W : World) (b lb : Word) (s t : PState) (X : List Byte) : Prop where
  rip : t.m.core.rip = W.gate
  rax : low32 (t.m.core.read .rax) = 0#32
  ghost : t.g.jobs = [.exitRax] ∧ t.g.atexit = [b + 0x69b0#64] ∧ t.g.done = none
  out : ∃ st, StdoutIs E t.m.memory st ∧ st.err = false ∧ st.reading = false ∧ t.g.out ++ st.buf = X
  err : E.S.file t.m.memory E.stderrF (outSt 2)
  vars : StdVars E W lb t.m.memory
  mem : ShaMem b lb t.m.memory ∧ ShaMemC b lb t.m.memory
  fs : t.m.core.fsBase = s.m.core.fsBase
  /-- `completed.0` (`0xa040`, read by `__do_global_dtors_aux`): still 0, writable -/
  bss : loadN t.m.memory (b + 0xa040#64) 1 = some 0#64 ∧ t.m.memory.Permitted .write (b + 0xa040#64).toNat 1

/-- **`main` has returned with status `code`** (K8: the generalisation of `MainRet` to any status,
used with 0 or 1 on the file-error tier), `stdout` holding `X` in total, `stderr` (`Ghost.err`)
holding `Y`. `MainRet` is the case `code = 0` (`MainRet.toG`). -/
structure MainRetG (E : Env) (W : World) (b lb : Word) (s t : PState) (X : List Byte) (code : BitVec 32)
    (Y : List Byte) : Prop where
  rip : t.m.core.rip = W.gate
  rax : low32 (t.m.core.read .rax) = code
  ghost : t.g.jobs = [.exitRax] ∧ t.g.atexit = [b + 0x69b0#64] ∧ t.g.done = none
  out : ∃ st, StdoutIs E t.m.memory st ∧ st.err = false ∧ st.reading = false ∧ t.g.out ++ st.buf = X
  err : E.S.file t.m.memory E.stderrF (outSt 2)
  vars : StdVars E W lb t.m.memory
  mem : ShaMem b lb t.m.memory ∧ ShaMemC b lb t.m.memory
  fs : t.m.core.fsBase = s.m.core.fsBase
  bss : loadN t.m.memory (b + 0xa040#64) 1 = some 0#64 ∧ t.m.memory.Permitted .write (b + 0xa040#64).toNat 1
  gerr : t.g.err = Y

theorem MainRet.toG {E : Env} {W : World} {b lb : Word} {s t : PState} {X : List Byte}
    (h : MainRet E W b lb s t X) : MainRetG E W b lb s t X 0#32 t.g.err :=
  ⟨h.rip, h.rax, h.ghost, h.out, h.err, h.vars, h.mem, h.fs, h.bss, rfl⟩

/-- **The layout facts at `main`'s entry that its tail uses** (beyond what `MainOpt` carries to
`0x29fd`): the return address is the library's gate; the code of all of `main`, `clearerr`'s GOT
slot and `completed.0` (image); libc's `stdin` variable holds `fi` (kept, outside the image,
apart from `argv[1]`'s slot); the guard (kept, outside the image); `argv[1]`'s slot (the
`NULL` that `main` overwrites with `"-"`): in the argument area above `main`'s frame, readable,
writable, apart from libc's stream variables and the guard. -/
structure TailEntry (E : Env) (W : World) (b lb : Word) (s : PState) (fi g : Word) : Prop where
  ret : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [W.gate])
  al : (s.m.core.read .rsp).toNat % 16 = 8
  lo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat
  mainAll : ShaMainAll b s.m.memory
  clr : loadN s.m.memory (b + 0x9f68#64) 8 = some (lb + 0x91400#64)
  bss : loadN s.m.memory (b + 0xa040#64) 1 = some 0#64
  bssw : s.m.memory.Permitted .write (b + 0xa040#64).toNat 1
  var : loadN s.m.memory (lb + 0x2056b0#64) 8 = some fi
  vark : ∀ j, j < 8 → W.Kept ((lb + 0x2056b0#64).toNat + j)
  varImg : ∀ j, j < 8 → ¬ ShaImg b ((lb + 0x2056b0#64).toNat + j)
  fi0 : fi ≠ 0#64
  fiO : fi ≠ E.stdoutF
  fiE : fi ≠ E.stderrF
  guard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j)
  guardImg : ∀ j, j < 8 → ¬ ShaImg b ((s.m.core.fsBase + 0x28#64).toNat + j)
  imgVar : ∀ a, ShaImg b a → ¬ VarR lb a
  argsImg : ∀ a, W.args a → ¬ ShaImg b a
  optK : ∀ a, OptR E a → ¬ W.Kept a
  avHi : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rsi).toNat
  av : (s.m.core.read .rsi).toNat + 16 < 2 ^ 64
  avA : ∀ j, j < 8 → W.args ((s.m.core.read .rsi).toNat + 8 + j)
  avR : s.m.memory.Permitted .read ((s.m.core.read .rsi).toNat + 8) 8
  avW : s.m.memory.Permitted .write ((s.m.core.read .rsi).toNat + 8) 8
  avVar : ∀ j, j < 8 → ¬ VarR lb ((s.m.core.read .rsi).toNat + 8 + j)
  avIn : (lb + 0x2056b0#64).toNat + 8 ≤ (s.m.core.read .rsi).toNat + 8 ∨
    (s.m.core.read .rsi).toNat + 16 ≤ (lb + 0x2056b0#64).toNat
  avG : (s.m.core.fsBase + 0x28#64).toNat + 8 ≤ (s.m.core.read .rsi).toNat + 8 ∨
    (s.m.core.read .rsi).toNat + 16 ≤ (s.m.core.fsBase + 0x28#64).toNat

/-- **`main` from `0x29fd` to its return**, stdin tier (proved: `TailAll.task_mainStdinTail`; it
composes the option checks, `argv[1] = "-"`, `Task.digestStdin`, `Task.printLine`,
`rpl_fclose (stdin)` and the epilogue). -/
def Task.mainStdinTail (E : Env) (W : World) (b lb kb sr sc : Word) : Prop :=
  ∀ (C : Nat → Prop) (fi : Word) (data : List Byte) (Q : PState → Prop) (s s1 z : PState) (g : Word),
    TailEntry E W b lb s fi g →
    MainOpt E W b lb kb sr sc C fi (outSt 1) (outSt 2) (stdinSt data) s s1 z g
      { s.g with atexit := [b + 0x69b0#64] } →
    s.g.out = [] → s.g.jobs = [.exitRax] →
    (s.g.allocs < E.maxAllocs ∧ s.g.heap + 0x8048 ≤ E.maxHeap) → s.g.done = none →
    BitVec.setWidth 32 (s.m.core.read .rdi) = 1#32 →
    (∀ t, MainRet E W b lb s t (stdinLine data) → MustQ W Q t) → MustQ W Q z

/-- What the end of the process needs of the world: the imports `close_stdout` calls, the
start-up facts (`ShaWorldOk`: image, eager binding, the fini array), `__cxa_finalize`'s binding,
reliable output, and two guarantees of the library while it runs the exit jobs: exit handlers
run on a stack above the streams (`atCall`), and the streams keep their states across the gate
(`atGate`). -/
structure ExitOk (E : Env) (W : World) (b lb : Word) : Prop where
  cl : CloseImps E W b lb
  wo : ShaWorldOk W b lb
  cxa : W.fns.find? (·.1 == lb + 0x472c0#64) = some (lb + 0x472c0#64, .cxaFinalize)
  cxa_out : ¬ ShaImg b (lb + 0x472c0#64).toNat
  gate_cxa : W.gate ≠ lb + 0x472c0#64
  cxa_ne : lb + 0x472c0#64 ≠ 0#64
  rel : W.reliable = true
  ne : E.stderrF ≠ E.stdoutF
  atCall : ∀ t, W.atCall t → E.S.lo + 1024 ≤ (t.m.core.read .rsp).toNat
  atGate : ∀ s t f st, W.atGate s t → E.S.file s.m.memory f st → E.S.file t.m.memory f st
  /-- The library buffers nothing outside the stream model when `main` returns (`World.pending`
  is empty; stdout's buffer is `E.S`'s and `close_stdout` flushes it). The default `pending`. -/
  pend : ∀ s p, W.pending s p → p = []

/-- **The end of the process** after `main` returned 0 (proved: `ExitPath.task_exitPath`; it
composes `sha_closeStdout`, the destructors and `_fini`, with `exit` emptying the handler list). -/
def Task.exitPath (E : Env) (W : World) (b lb : Word) : Prop :=
  ExitOk E W b lb → ∀ (s t : PState) (X : List Byte), MainRet E W b lb s t X → MustQ W (Ended 0 fun w => w = X) t

/-- **The end of the process** after `main` returned `code` (K8; proved: `ExitPath.task_exitPathG`):
the process halts with status `code` (a byte, so `code < 256`), `stdout` holding `X` and `stderr`
`Y` (nothing is written to `stderr` at exit). -/
def Task.exitPathG (E : Env) (W : World) (b lb : Word) : Prop :=
  ExitOk E W b lb → ∀ (s t : PState) (X : List Byte) (code : BitVec 32) (Y : List Byte), code.toNat < 256 →
    MainRetG E W b lb s t X code Y → MustQ W (fun u => Ended code.toNat (fun w => w = X) u ∧ u.g.err = Y) t

set_option maxRecDepth 100000 in
/-- **sha256sum, stdin tier, from `main`'s entry**: every run ends with status 0 having written
`stdinLine data` (= the specification's record, `stdinLine_spec`), given the two open goals. -/
theorem sha_main_stdin {E : Env} {W : World} {b lb kb sr sc : Word} (I : MainImps E W b lb sr)
    (T1 : Task.mainStdinTail E W b lb kb sr sc) (T2 : Task.exitPath E W b lb) (XO : ExitOk E W b lb)
    {C : Nat → Prop} {fi : Word} {s : PState} {a0p : Word} {a0 data : List Byte} {g : Word}
    (h : MainEntryS E W b lb kb sr sc C fi s a0p a0 data g) (ht : TailEntry E W b lb s fi g) :
    MustQ W (Ended 0 fun w => w = stdinLine data) s := by
  have hal := h.abi.aligned
  obtain ⟨hd, hat, hout, hjobs⟩ := h.ghost
  refine sha_main_head I.img I.hb I.lz I.strrchr I.loc (privKeep E) h.rip h.abi h.room hd h.mem h.rw h.lo h.env
    h.hC h.pinC h.pinK h.lbB h.imgVar h.argsImg h.argv0 h.argv0k h.a0s h.a0k h.a0nz h.noSlash h.guard h.guardk ?_
  intro s1 x hL
  refine sha_main_buf I.img I.hb I.lz I.atexit I.setvbuf hL (by rw [hL.g]; exact hat) hal h.lo h.hC ?_
  intro y hM
  refine sha_main_getopt I.img I.hb I.lz I.getopt hM hal h.lo h.hC h.optC h.optK h.optL h.opt
    (args := [a0]) (by rw [h.argc]; rfl) h.argv (by simp) ?_
  intro z hO
  exact T1 C fi data _ s s1 z g ht hO hout hjobs h.res hd h.argc fun t ht => T2 XO s t _ ht

/-- The specification world of a stdin-tier run: program name `prog`, standard input `data`. -/
def stdinWorld (prog data : List Byte) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) : Silmaril.Apps.Sha256sum.World :=
  { argv := [toSpec prog], posix, fs, stdin := .bytes (toSpec data) }

/-- **sha256sum, stdin tier, against the specification** `Apps.Sha256sum.sha256sum`: the run's
exit status and standard output are the specification's (stderr is not modelled; the
specification's is empty on this tier). -/
theorem sha_main_stdin_spec {E : Env} {W : World} {b lb kb sr sc : Word} (I : MainImps E W b lb sr)
    (T1 : Task.mainStdinTail E W b lb kb sr sc) (T2 : Task.exitPath E W b lb) (XO : ExitOk E W b lb)
    {C : Nat → Prop} {fi : Word} {s : PState} {a0p : Word} {a0 data : List Byte} {g : Word}
    (h : MainEntryS E W b lb kb sr sc C fi s a0p a0 data g) (ht : TailEntry E W b lb s fi g) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) :
    MustQ W (Ended (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).status fun w =>
      w = (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).stdout.map UInt8.toBitVec ∧
      (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).stderr = []) s := by
  have hspec := Silmaril.Apps.Sha256sum.Sys.sha256sum_stdin (toSpec a0) posix fs (toSpec data)
  simp only [stdinWorld, hspec, ← stdinLine_spec, and_true]
  exact sha_main_stdin I T1 T2 XO h ht

end Silmaril.Elf.Link.Dyn.Sha256sum
