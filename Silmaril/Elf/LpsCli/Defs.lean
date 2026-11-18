module

public import Silmaril.Cli.Institution.Defs
public import Silmaril.Process.LPS.ELFImageX86
public import Silmaril.Process.LPS.Machines.X86NativeLaunch
public import Silmaril.Process.LPS.Machines.X86FlagChoices8

/-!
# Static x86-64 executables under LPS as models of the CLI institution (level `L1`)

A statically linked x86-64 ELF has no loader or shared library to model: its whole run is the
launch of its `PT_LOAD` segments into a process of LPS (`Silmaril.Process.LPS`, the Lean port
of rocq-linux-process-semantics) and the user machine's steps between system calls. This module
reads that semantics as an `L1` model of the CLI institution (`Silmaril.Cli.Institution`): stdin in,
stdout and exit code out.

* `lpsBytes`: CLI bytes as LPS bytes (`UInt8` to `BitVec 8`).
* `Visible e`, `exitOf tr`, `stdoutOf tr`, `out1Of tr`: the `L1` observation of an LPS trace.
  A trace is **ended** when its last event other than a kill is an exit; the observation is the
  bytes written to channel `1` and the status as an exit code (`UInt8.ofNat`, so modulo 256).
  Kill events are skipped, as `Silmaril.Sim.WasiBridge.obsOfEvent` skips them, so that the model is
  literally the trace model of the ELF ≡ WASI bridge (`Silmaril.Sim.WasiBridge.Lps`).
* `StdinLaunch isa file s oracle en inp`: a launch of the **stdin tier**: the file parses as an
  x86-64 ELF (`ELFImage.parse x86Policy`), stdin is the finite stream `s`, `argv` has one
  element (the program name, any), the input and entry are valid for the snapshot. Environment,
  file system, entry addresses and the program name are arbitrary.
* `lpsModel isa file` (`L1`): a run on stdin `s` with observation `o` is an ended trace of
  `X86NativeLaunch.runWith (isa oracle) refusals snapshot limit en inp` for some flag oracle,
  refusal configuration, budget and stdin-tier launch, with `out1Of tr = some o`. Partial
  correctness: runs that fault, diverge or are unmodelled have no observation, and a sentence
  says nothing about them.
* `ext8`: the machine family of the sha256sum release statements (`x86WithFlagOracle8`, native
  x86-64 with the 8-bit ALU forms, an explicit oracle for flags undefined at `syscall`), the
  default.
* `filterTrace m out fs`: the complete trace of a stdin filter: read `m`, write `out` to
  channel 1, exit 0 with the file system `fs`. Silmaril's LPS release statements
  (`Sha256Cli.idealTrace`, `GnuSha256sum.idealTrace`) are of this form.

`Thms`: `out1Of_of_prefix` (a prefix of `filterTrace m out fs` that ends observes `out`, exit 0),
and the reusable rule `sat_filter_of_prefix`: an LPS release statement of the shape "every trace
of every admissible launch is a prefix of `filterTrace`" makes `lpsModel` a model of
`Sen.filter`. The pinned binaries are in `Silmaril.Elf.LpsCli.Sha256sum`.

**Trust.** Statements about LPS with the handwritten `X86.Ext`/`Ext8` instruction semantics, not
about Linux or hardware; that `file` is the executable is a byte comparison done outside Lean.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Elf.LpsCli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Cli.Institution (Level Model Out1)

/-- An oracle for flags that are undefined at a `syscall`. -/
abbrev Oracle := Nat → X86FlagChoices.Choice

/-- A user machine for every flag oracle. -/
abbrev Isa := Oracle → UserIsa

/-- **The machine of the sha256sum release statements**: `x86WithFlagOracle8`. -/
abbrev ext8 : Isa := x86WithFlagOracle8

/-- **The machine of the `sha256` filter's release statements**: `x86WithFlagOracle`. -/
abbrev ext : Isa := x86WithFlagOracle

/-- CLI bytes as LPS bytes. -/
def lpsBytes (s : Silmaril.Cli.Bytes) : List Byte := s.map UInt8.toBitVec

/-- LPS bytes as CLI bytes. -/
def cliBytes (b : List Byte) : Silmaril.Cli.Bytes := b.map UInt8.ofBitVec

/-- Every event but a kill is visible to the CLI. -/
def Visible : Event → Bool
  | .killEv .. => false
  | _ => true

/-- The exit status of an ended trace: its last visible event is an exit. -/
def exitOf (tr : List Event) : Option Word :=
  match (tr.filter Visible).getLast? with
  | some (.exitEv c _) => some c
  | _ => none

/-- The bytes written to channel `1`. -/
def stdoutOf (tr : List Event) : List Byte :=
  tr.filterMap fun
    | .writeEv ch b => if ch.toNat = 1 then some b else none
    | _ => none

/-- **The `L1` observation of an ended LPS trace.** -/
def out1Of (tr : List Event) : Option Out1 :=
  (exitOf tr).map fun c => { stdout := cliBytes (stdoutOf tr), exit := UInt8.ofNat c.toNat }

/-- **A launch of the stdin tier.** -/
def StdinLaunch (isa : Isa) (file : Silmaril.Formats.ELF.Bytes) (s : Silmaril.Cli.Bytes)
    (oracle : Oracle) (en : ExecEntry) (inp : ProcInput) (records : ELFImage.Records) : Prop :=
  ELFImage.parse ELFImage.x86Policy file = some records ∧
    inp.stdin = InputStream.ofList (lpsBytes s) ∧ inp.argv.length = 1 ∧ X86Launch.ValidInput inp ∧
    X86Launch.ValidEntry (isa oracle) (records.x86Snapshot file) en inp

/-- The LPS behaviour of a launch of `file`. -/
def behaviour (isa : Isa) (file : Silmaril.Formats.ELF.Bytes) (records : ELFImage.Records)
    (oracle : Oracle) (refusals : SpuriousCfg) (limit : Int) (en : ExecEntry) (inp : ProcInput) :
    Behavior :=
  X86NativeLaunch.runWith (isa oracle) refusals (records.x86Snapshot file) limit en inp

/-- The LPS traces of the stdin tier of `file` on stdin `s`. -/
def StdinTrace (isa : Isa) (file : Silmaril.Formats.ELF.Bytes) (s : Silmaril.Cli.Bytes)
    (tr : List Event) : Prop :=
  ∃ (oracle : Oracle) (refusals : SpuriousCfg) (limit : Int) (en : ExecEntry) (inp : ProcInput)
    (records : ELFImage.Records),
    StdinLaunch isa file s oracle en inp records ∧
      (behaviour isa file records oracle refusals limit en inp).traces tr

/-- **A static x86-64 executable under LPS** (level `L1`). -/
def lpsModel (file : Silmaril.Formats.ELF.Bytes) (isa : Isa := ext8) : Model Level.stream.sig :=
  ⟨fun s o => ∃ tr, StdinTrace isa file s tr ∧ out1Of tr = some o⟩

/-- **The complete trace of a stdin filter**: read `m`, write `out` to channel 1, exit 0. -/
def filterTrace (m out : List Byte) (fs : Fs.FileSystem) : List Event :=
  m.map (Event.readEv 0) ++ out.map (Event.writeEv 1) ++ [Event.exitEv 0 fs]

end Silmaril.Elf.LpsCli
