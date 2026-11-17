module

public import Silmaril.Sim.WasiBridge.Cli.Defs
public import Silmaril.Elf.LpsCli.Defs
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Elf

/-!
# Static executables under LPS as trace semantics of the ELF ≡ WASI bridge

`lpsTraces file isa s` is the observable traces (`obsTrace`) of the stdin-tier LPS launches of
a static x86-64 executable (`Silmaril.Elf.LpsCli.StdinTrace`). `Thms` proves that the
CLI model `LpsCli.lpsModel file isa` **is** `traceModel (lpsTraces file isa)`, so every theorem
about trace models (`sat_iff_of_elfWasiEquiv`, `traceModel_mono`) applies to static executables
under LPS, and the pinned `sha256sum-min` discharges `Task.wasiSha256` for any WASI program
equivalent to it (`Thms`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.Lps

open Silmaril.Elf.LpsCli (Isa ext8 StdinTrace)

/-- **The observable traces of a static executable's stdin tier under LPS.** -/
def lpsTraces (file : Silmaril.Formats.ELF.Bytes) (isa : Isa := ext8) (s : Silmaril.Cli.Bytes)
    (t : List Obs) : Prop :=
  ∃ tr, StdinTrace isa file s tr ∧ t = obsTrace tr

/-- One observable per visible event. -/
def obs1 : Silmaril.Process.LPS.Event → Obs
  | .readEv ch b => .rd ch.toNat b
  | .writeEv ch b => .wr ch.toNat b
  | .exitEv c _ => .exit c.toNat
  | .killEv .. => .rd 0 0

/-- The traces of `sha256sum-min` under LPS. -/
abbrev staticTraces : Silmaril.Cli.Bytes → List Obs → Prop :=
  lpsTraces Silmaril.Process.LPS.Problems.GnuSha256sum.file ext8

end Silmaril.Sim.WasiBridge.Lps
