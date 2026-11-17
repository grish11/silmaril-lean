module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainGetopt
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestSpec
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.PrintHex
public import Silmaril.Apps.Sha256sum.StdinRef

/-! # GNU `sha256sum`, stdin tier: the statements of the remaining pieces

With no operand, `main` digests standard input (`digest_file ("-", …)`), prints
`hex(SHA-256(stdin)) ++ "  -\n"`, closes standard input (`rpl_fclose (stdin)`) and returns 0;
`exit` then runs `close_stdout`, the destructors and `_fini`.

* `digest_file ("-", …)` on standard input: `DigestStdin.task_digestStdin` (proved).
* `Task.printLine`: the result line, `0x2b8a` → `0x2c8a` (`PrintEntry` → `PrintExit`): `stdout`
  receives `hexOf digest ++ "  " ++ name ++ "\n"`.
* `stdinLine`: the bytes of the line; `stdinLine_spec`: they are the specification's record
  `Apps.Sha256sum.Sys.stdinRecord` (proved).
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

/-! ## The bytes of the line -/

/-- The result line for standard input: `hex(SHA-256(data)) ++ "  -\n"`. -/
def stdinLine (data : List Byte) : List Byte := hexOf (sha256 data) ++ [0x20#8, 0x20#8, 0x2d#8, 0x0a#8]

theorem hex2_spec (u : UInt8) :
    hex2 u.toBitVec = [Silmaril.Apps.Sha256sum.hexDigit (u.toNat / 16),
      Silmaril.Apps.Sha256sum.hexDigit (u.toNat % 16)].map UInt8.toBitVec := by
  have h1 : u.toNat / 16 < 16 := by have := u.toNat_lt; omega
  have h2 : u.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  simp only [hex2, Silmaril.Apps.Sha256sum.hexDigit, List.map_cons, List.map_nil, UInt8.toNat_toBitVec,
    List.cons.injEq, and_true]
  constructor <;> split <;> rfl

/-- **The line is the specification's stdin record.** -/
theorem stdinLine_spec (data : List Byte) :
    stdinLine data = (Silmaril.Apps.Sha256sum.Sys.stdinRecord (toSpec data)).map UInt8.toBitVec := by
  simp only [stdinLine, hexOf, sha256, Silmaril.Apps.Sha256sum.Sys.stdinRecord,
    Silmaril.Apps.Sha256sum.hexDigest, Silmaril.Apps.Sha256sum.hexLower, toSpec, List.map_append,
    List.flatMap_map, List.map_flatMap]
  congr 1
  exact List.flatMap_congr fun u _ => hex2_spec u

/-! ## `digest_file` on standard input -/

/-- The stream state of standard input with `data` unread. -/
def stdinSt (data : List Byte) : St := ⟨0, true, data, false, false, false, []⟩

/-! ## The result line -/

/-- What the result line's code (`0x2b8a`) needs, inside `main`'s body (base `s1`, `main`'s entry
stack pointer `sp`): the digest at `rbp - 0x60`, the name in `r12`, the flags in the frame. -/
structure PrintEntry (E : Env) (W : World) (b lb sc : Word) (s1 u : PState) (sp : Word)
    (dg name : List Byte) (st : St) : Prop where
  body : Body W (ShaMemP b lb sc) s1 u 328 4096 (sv6 s1)
  hsp : s1.m.core.read .rsp = sp
  rip : u.m.core.rip = b + 0x2b8a#64
  rbp : u.m.core.read .rbp = sp - 8#64
  rbx : u.m.core.read .rbx = sp - 8#64 - 0x60#64
  r14 : u.m.core.read .r14 = b + 0x7238#64
  hdg : u.m.memory.readBytes (sp - 8#64 - 0x60#64).toNat 32 = some dg
  dglen : dg.length = 32
  hname : CStr u.m.memory (u.m.core.read .r12) name
  namek : ∀ j, j < name.length + 1 → W.Kept ((u.m.core.read .r12).toNat + j)
  /-- the name is not library-private (the `strcspn` and `fputs_unlocked` frames keep only
  non-private memory) -/
  namep : ∀ j, j < name.length + 1 → ¬ E.S.priv u.m.memory ((u.m.core.read .r12).toNat + j)
  noEsc : ∀ c ∈ name, c ≠ 0x5c#8 ∧ c ≠ 0x0a#8 ∧ c ≠ 0x0d#8
  /-- `--tag` false (`rbp - 0xd0`), `binary = -1` (`rbp - 0xc8`) -/
  tag : u.m.memory.readBytes (sp.toNat - 216) 1 = some [0#8]
  binary : u.m.memory.readBytes (sp.toNat - 208) 4 = some [0xff#8, 0xff#8, 0xff#8, 0xff#8]
  /-- the delimiter `'\n'` and `digest_hex_bytes = 64` -/
  delim : u.m.memory.readBytes (b + 0xa01c#64).toNat 1 = some [0x0a#8]
  hexLen : loadN u.m.memory (b + 0xa178#64) 8 = some 0x40#64
  stdout : StdoutIs E u.m.memory st
  stdoutErr : st.err = false
  vars : StdVars E W lb u.m.memory
  footK : ∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a
  fw : E.stdoutF.toNat + 0x38 < 2 ^ 64
  lo : E.S.lo + 4096 ≤ sp.toNat
  al : sp.toNat % 16 = 8
  rel : W.reliable = true

/-- What the result line guarantees at `0x2c8a`. -/
structure PrintExit (E : Env) (W : World) (b lb sc : Word) (s1 u v : PState) (sp : Word)
    (dg name : List Byte) (st : St) : Prop where
  body : Body W (ShaMemP b lb sc) s1 v 328 4096 (sv6 s1)
  rip : v.m.core.rip = b + 0x2c8a#64
  rsp : v.m.core.read .rsp = u.m.core.read .rsp
  /-- the callee-saved registers but `r13` (the hex loop's counter) -/
  cs : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], v.m.core.read r = u.m.core.read r
  /-- `stdout` received the line -/
  out : ∃ st', StdoutIs E v.m.memory st' ∧ st'.err = false ∧ st'.rd = st.rd ∧ st'.eof = st.eof ∧ st'.reading = st.reading ∧
    v.g.out ++ st'.buf = u.g.out ++ st.buf ++ hexOf dg ++ [0x20#8, 0x20#8] ++ name ++ [0x0a#8]
  ghost : v.g.jobs = u.g.jobs ∧ v.g.atexit = u.g.atexit ∧ v.g.done = none ∧ v.g.inp = u.g.inp ∧
    v.g.allocs = u.g.allocs ∧ v.g.heap = u.g.heap ∧ v.g.files = u.g.files
  /-- the frame keeps everything but the two slots the code writes (`rbp - 0xf8`, `rbp - 0xec`) -/
  frame : Keeps (fun a => (W.Kept a ∨ sp.toNat - 328 ≤ a) ∧ ¬ (sp.toNat - 256 ≤ a ∧ a < sp.toNat - 252) ∧
    a ≠ sp.toNat - 244) u.m.memory v.m.memory
  streams : ∀ f st', f ≠ E.stdoutF → E.S.file u.m.memory f st' → E.S.file v.m.memory f st'
  /-- nothing written to `stderr` -/
  gerr : v.g.err = u.g.err
  /-- the library variables (`program_invocation_name`, …) are kept -/
  lib : LibK E W u.m.memory v.m.memory

/-- **The result line** (proved: `PrintTask.task_printLine`). `PutcLaw` and `StreamsDisj` are
assumptions on the stream representation. -/
def Task.printLine (E : Env) (W : World) (b lb sc : Word) : Prop :=
  PrintImps E W b lb sc → PutcLaw E → StreamsDisj E → ∀ (Q : PState → Prop) (s1 u : PState) (sp : Word) (dg name : List Byte) (st : St),
    PrintEntry E W b lb sc s1 u sp dg name st →
    (∀ v, PrintExit E W b lb sc s1 u v sp dg name st → MustQ W Q v) → MustQ W Q u

end Silmaril.Elf.Link.Dyn.Sha256sum
