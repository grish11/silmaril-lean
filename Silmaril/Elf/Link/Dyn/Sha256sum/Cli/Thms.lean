module

public import Silmaril.Elf.Link.Dyn.Sha256sum.Cli.Defs
public import Silmaril.Elf.Link.Dyn.Program.Cli.Thms
public import Silmaril.Cli.Institution.Std.Defs
import Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.Cli

/-!
# GNU `sha256sum` on glibc satisfies the stdin digest filter

PROVED (standard axioms):

* **`stdinModel_sat`**: the `L1` model of the pinned GNU `sha256sum` on glibc satisfies
  `Sen.filter stdinRecord` (stdout `hex(SHA-256(d)) ++ "  -\n"`, exit `0`, for every stdin `d`),
  from `Sha256sum.sha256sum_stdin` and silmaril's `Sys.sha256sum_stdin`; `stdinModel_std`: the
  same as the standard sentence `Std.sha256Stdin`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Cli.Institution (Level Model Sen Out1)



/-- **GNU `sha256sum` on glibc prints the digest line of its stdin and exits `0`.** -/
theorem stdinModel_sat : stdinModel.Sat (Sen.filter stdinRecord) :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.Cli.stdinModel_sat

/-- GNU `sha256sum` on glibc meets the standard `L1` sentence `Std.sha256Stdin`. -/
theorem stdinModel_std : stdinModel.Sat Silmaril.Cli.Institution.Std.sha256Stdin :=
  Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.Cli.stdinModel_std

end Silmaril.Elf.Link.Dyn.Sha256sum
