module

public import Silmaril.Elf.Link.Dyn.Sha256sum.Run.Thms
public import Silmaril.Elf.Link.Dyn.Program.Cli.Defs

/-!
# GNU `sha256sum` on glibc as a model of the CLI institution (stdin, level `L1`)

`stdinModel` is the `L1` semantics of the pinned GNU `sha256sum` (coreutils 9.4, Ubuntu,
`examples/elf/pinned/gnu-sha256sum`) on glibc, from the end-to-end development `Silmaril.Elf.Link.Dyn.Sha256sum`:
a run on stdin `d` is a load of the executable with `libcrypto.so.3`, `libc.so.6` and `ld.so`
agreeing with the pinned chunks (any bases, ifunc choice and binding mode), a start state the
kernel may produce (`ShaStartState`), a world with the imports' contracts (`MainImps`,
`TailImps`, `ExitOk`) and resource bounds whose library enters `main` with `argv = [a0]` (any
program name) and stdin `d` (`MainLib`), and a finite run of the process machine to an ended
state; its observation is the bytes on fd 1 and the status.

The hypotheses are exactly those of `Sha256sum.sha256sum_stdin`, so the trusted base is that
theorem's (the import contracts, the stream representation, the loader relation, the process
machine). `Thms`: `stdinModel_sat`, the binary is a model of the stream filter
`d ↦ hex(SHA-256(d)) ++ "  -\n"`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports
open Silmaril.Cli.Institution (Level Model Out1)

/-- **A run of GNU `sha256sum` on stdin `d`, observed as `o`.** -/
def StdinRun (d : Silmaril.Cli.Bytes) (o : Out1) : Prop :=
  ∃ (Fk Fc Fl : Blob) (b kb lb ldb res sr sc : Word) (ifn : Word → Option Word) (lazy : Bool)
    (E : Env) (R : ShaRep) (W : World) (s : PState) (argc : Word) (a0 : List Byte) (u : PState)
    (e : Nat) (out : List Byte),
    ChunksOf Fk cryptoChunks ∧ ChunksOf Fc libcChunks ∧ ChunksOf Fl ldChunks ∧
    ifn (lb + 0xb5210#64) = some sr ∧ ifn (lb + 0xb4410#64) = some sc ∧
    MainImps E W b lb sr ∧ TailImps E R W b lb kb sc ∧ ExitOk E W b lb ∧
    ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn lazy res s.m.memory ∧
    ShaStartState W b s argc ∧ (1 ≤ E.maxAllocs ∧ 0x8048 ≤ E.maxHeap) ∧
    (∀ t, W.atMain t → ∃ C fi a0p g, MainLib E W b lb C fi t a0p a0 (ofSpec d) g) ∧
    Relation.ReflTransGen (Program.OkStep W) s u ∧ u.g.done = some (e, out) ∧
    o = { stdout := toSpec out, exit := UInt8.ofNat e }

/-- **The `L1` CLI model of GNU `sha256sum` on glibc.** -/
def stdinModel : Model Level.stream.sig := ⟨StdinRun⟩

end Silmaril.Elf.Link.Dyn.Sha256sum
