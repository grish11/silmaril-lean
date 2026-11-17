module

public import Silmaril.Elf.LpsCli.Defs
import Silmaril.Proofs.Elf.LpsCli.Filter

/-!
# Static executables under LPS: the filter rule

PROVED (standard axioms):

* `cliBytes_lpsBytes`: the byte conversions are inverse;
* `exitOf_eq_none`: a trace without an exit event has not ended;
* `out1Of_filterTrace`: the complete filter trace observes `out` and exit `0`;
* **`out1Of_of_prefix`**: an ended prefix of `filterTrace m out fs` is the whole trace, so it
  observes `out` and exit `0`;
* **`sat_filter_of_prefix`**: the reusable rule. An LPS release statement "every trace of every
  stdin-tier launch is a prefix of `filterTrace (stdin) (f stdin)`" (the `safe` field of the
  `Partial` structures of silmaril's `Sha256Cli` and `GnuSha256sum` statements) makes
  `lpsModel file isa` a model of `Sen.filter f`.
-/

@[expose] public section

namespace Silmaril.Elf.LpsCli

open Silmaril.Process.LPS
open Silmaril.Cli.Institution (Level Model Out1 Sen)

@[simp] theorem cliBytes_lpsBytes (s : Silmaril.Cli.Bytes) : cliBytes (lpsBytes s) = s :=
  Silmaril.Proofs.Elf.LpsCli.cliBytes_lpsBytes s

@[simp] theorem lpsBytes_cliBytes (b : List Byte) : lpsBytes (cliBytes b) = b :=
  Silmaril.Proofs.Elf.LpsCli.lpsBytes_cliBytes b

theorem exitOf_eq_none {tr : List Event} (h : ∀ e ∈ tr, ∀ c fs, e ≠ .exitEv c fs) :
    exitOf tr = none :=
  Silmaril.Proofs.Elf.LpsCli.exitOf_eq_none h

theorem stdoutOf_filterTrace (m out : List Byte) (fs : Fs.FileSystem) :
    stdoutOf (filterTrace m out fs) = out :=
  Silmaril.Proofs.Elf.LpsCli.stdoutOf_filterTrace m out fs

theorem exitOf_filterTrace (m out : List Byte) (fs : Fs.FileSystem) :
    exitOf (filterTrace m out fs) = some 0 :=
  Silmaril.Proofs.Elf.LpsCli.exitOf_filterTrace m out fs

theorem out1Of_filterTrace (m out : List Byte) (fs : Fs.FileSystem) :
    out1Of (filterTrace m out fs) = some { stdout := cliBytes out, exit := 0 } :=
  Silmaril.Proofs.Elf.LpsCli.out1Of_filterTrace m out fs

/-- **An ended prefix of a filter trace is the whole trace.** -/
theorem out1Of_of_prefix {tr : List Event} {m out : List Byte} {fs : Fs.FileSystem} {o : Out1}
    (h : tr <+: filterTrace m out fs) (ho : out1Of tr = some o) :
    o = { stdout := cliBytes out, exit := 0 } :=
  Silmaril.Proofs.Elf.LpsCli.out1Of_of_prefix h ho

/-- **The filter rule.** -/
theorem sat_filter_of_prefix {isa : Isa} {file : Silmaril.Formats.ELF.Bytes}
    {f : Silmaril.Cli.Bytes → Silmaril.Cli.Bytes}
    (h : ∀ s oracle refusals limit en inp records tr,
      StdinLaunch isa file s oracle en inp records →
      (behaviour isa file records oracle refusals limit en inp).traces tr →
      tr <+: filterTrace (lpsBytes s) (lpsBytes (f s)) inp.fs) :
    (lpsModel file isa).Sat (Sen.filter f) :=
  Silmaril.Proofs.Elf.LpsCli.sat_filter_of_prefix h

end Silmaril.Elf.LpsCli
