module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesFrame
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesNull
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestSpec

/-! # GNU `sha256sum`: the statement of `digest_file` on a file that cannot be opened

```
0x6b90: fp = fopen_safer (filename, "r");            // NULL, errno = e
0x6ba9: if (fp == NULL) {
0x6cce:   if (ignore_missing && errno == ENOENT) …     // ignore_missing is false here
0x6ceb:   error (0, errno, "%s", quotef (filename));
0x6d14:   return false; }
```
`Task.digestOpenErr`: from `digest_file`'s entry on a name the file system refuses with `e`,
every run returns `false` having appended `prog: quotef(name): strerror(e)\n` to standard error
(`prog` is what `program_invocation_name` points to), with everything handed to standard output as
it was, the caller's data (but `*missing` and gnulib's `slot0`), the other streams, the library's
non-private memory, `fsBase` and the stack permissions kept.
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

/-- The imports of the error path, with `error`'s program-name variable at `pinA`. -/
structure ErrImps (E : Env) (W : World) (lb pinA : Word) : Prop where
  errno : ImpOk W (lb + 0x2a6e0#64) (nm "__errno_location") (errnoLocStep E W)
  error : ImpOk W (lb + 0x11e6c0#64) (nm "error") (errorMsgStep E pinA W)

/-- Memory a call of `digest_file` keeps besides the caller's: mapped, non-private bytes below the
streams (the library's variables, such as `program_invocation_name`) or at and above the caller's
stack pointer, other than `slot0` and the two result objects. -/
def NPo (E : Env) (b : Word) (s : PState) (a : Nat) : Prop :=
  ¬ E.S.priv s.m.memory a ∧ s.m.memory.permits .read a = true ∧ ¬ Slot0 b a ∧ ¬ DX s a ∧
    (a < E.S.lo ∨ (s.m.core.read .rsp).toNat ≤ a)

/-- What `digest_file`'s caller provides when the name cannot be opened. -/
structure DigEntryE (E : Env) (W : World) (b lb kb pinA : Word) (s : PState) (p : List Byte)
    (e : Silmaril.Apps.Sha256sum.Errno) (g : Word) (prog : List Byte) : Prop where
  rip : s.m.core.rip = b + 0x6a40#64
  abi : AbiEntry s.m.core s.m.memory
  room : Room W s.m.memory (s.m.core.read .rsp) 3072
  lo : E.S.lo + 3072 ≤ (s.m.core.read .rsp).toNat
  done : s.g.done = none
  mem : ShaMemCD b lb kb s.m.memory
  memK : ShaMemK b lb s.m.memory
  ro : ShaRO b lb s.m.memory
  qimps : QImps E W b lb s.m.memory
  slots : QSlots b s.m.memory
  slot0 : ∀ a, Slot0 b a → s.m.memory.permits .read a = true ∧ s.m.memory.permits .write a = true ∧
    ¬ E.S.priv s.m.memory a
  name : CStr s.m.memory (s.m.core.read .rdi) p
  namek : ∀ j, j < p.length + 1 → W.Kept ((s.m.core.read .rdi).toNat + j) ∧
    ¬ Slot0 b ((s.m.core.read .rdi).toNat + j)
  notDash : ∀ c0, s.m.memory.readBytes (s.m.core.read .rdi).toNat 1 = some [c0] → c0 ≠ 0x2d#8
  file : E.fs (toSpec p) = .openErr e
  fits : (Silmaril.Apps.Sha256sum.quotef (toSpec p)).length < 256
  outs : ∀ a, DX s a → ¬ W.Kept a ∧ (s.m.core.read .rsp).toNat + 8 ≤ a
  binw : s.m.memory.Permitted .write (s.m.core.read .rsi).toNat 32
  binr : s.m.memory.Permitted .read (s.m.core.read .rsi).toNat 32
  missw : s.m.memory.Permitted .write (s.m.core.read .rdx).toNat 1
  missr : s.m.memory.Permitted .read (s.m.core.read .rdx).toNat 1
  guard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j)
  guardq : ∀ j, j < 8 → ¬ Slot0 b ((s.m.core.fsBase + 0x28#64).toNat + j)
  /-- `errno` (thread-local storage) lies below the streams, away from the stack -/
  errnoLo : E.errnoA.toNat + 4 ≤ E.S.lo
  /-- `program_invocation_name` names `prog`; the variable is library memory the run keeps -/
  progN : ProgName s.m.memory pinA prog
  pin : ∀ j, j < 8 → NPo E b s (pinA.toNat + j)
  progk : ∀ pa, loadN s.m.memory pinA 8 = some pa → ∀ j, j < prog.length + 1 →
    W.Kept (pa.toNat + j) ∧ ¬ Slot0 b (pa.toNat + j)

/-- What `digest_file` guarantees when the name cannot be opened. -/
structure DigErrExit (E : Env) (W : World) (b : Word) (s t : PState) (p : List Byte)
    (e : Silmaril.Apps.Sha256sum.Errno) (prog : List Byte) : Prop where
  abi : AbiReturn s.m.core s.m.memory t.m.core
  keep : Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) ∧ ¬ (MX s a ∨ Slot0 b a))
    s.m.memory t.m.memory
  ret : low32 (t.m.core.read .rax) = 0#32
  gerr : t.g.err = s.g.err ++ errorMsg prog (ofSpec (Silmaril.Apps.Sha256sum.quotef (toSpec p))) e
  gjobs : t.g.jobs = s.g.jobs
  gatexit : t.g.atexit = s.g.atexit
  gdone : t.g.done = s.g.done
  ginp : t.g.inp = s.g.inp
  out : Appended E W s t []
  streams : ∀ f st, f ≠ E.stdoutF → E.S.file s.m.memory f st → E.S.file t.m.memory f st
  fs : t.m.core.fsBase = s.m.core.fsBase
  perm : PermKept s t.m.memory
  slots : QSlots b t.m.memory
  slot0 : ∀ a, Slot0 b a → t.m.memory.permits .read a = true ∧ t.m.memory.permits .write a = true ∧
    ¬ E.S.priv t.m.memory a
  lib : Keeps (NPo E b s) s.m.memory t.m.memory
  npriv : ∀ a, NPo E b s a → ¬ E.S.priv t.m.memory a
  /-- the permissions of `*missing` are as at entry (the error path does not write it after
  `*missing = false`) -/
  permMX : ∀ a, MX s a → ∀ acc, t.m.memory.permits acc a = s.m.memory.permits acc a
  /-- the library's resource counters are as at entry (`fopen` returned `NULL`) -/
  gallocs : t.g.allocs = s.g.allocs
  gheap : t.g.heap = s.g.heap
  gfiles : t.g.files = s.g.files

/-- **`digest_file` on a name the file system refuses** (open). -/
def Task.digestOpenErr (E : Env) (R : ShaRep) (W : World) (b lb kb pinA : Word) : Prop :=
  DigImps E R W b lb kb → ErrImps E W lb pinA → Task.quotef E W b lb →
    ∀ (Q : PState → Prop) (s : PState) (p : List Byte) (e : Silmaril.Apps.Sha256sum.Errno) (g : Word)
      (prog : List Byte), DigEntryE E W b lb kb pinA s p e g prog →
      (∀ t, DigErrExit E W b s t p e prog → MustQ W Q t) → MustQ W Q s

/-- `toSpec` undoes `ofSpec`. -/
theorem toSpec_ofSpec (l : Silmaril.Apps.Sha256sum.Bytes) : toSpec (ofSpec l) = l := by
  simp [toSpec, ofSpec, Function.comp_def]

/-- The diagnostic `digest_file` appends is the specification's `diagE` of the operand. -/
theorem toSpec_errMsg (prog p : List Byte) (e : Silmaril.Apps.Sha256sum.Errno) :
    toSpec (errorMsg prog (ofSpec (Silmaril.Apps.Sha256sum.quotef (toSpec p))) e) =
      Silmaril.Apps.Sha256sum.diagE (toSpec prog) (Silmaril.Apps.Sha256sum.quotef (toSpec p)) e := by
  rw [toSpec_errorMsg, toSpec_ofSpec]

end Silmaril.Elf.Link.Dyn.Sha256sum
