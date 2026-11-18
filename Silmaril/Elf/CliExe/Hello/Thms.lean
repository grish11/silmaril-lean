module

public import Silmaril.Elf.CliExe.Hello.Defs
import Silmaril.Proofs.Elf.CliExe.Hello

/-! # `hello-gcc` as a CLI executable: proved

PROVED (standard axioms), proofs in `Silmaril.Proofs.Elf.CliExe.Hello`:

* `helloOk`: the glibc loading facts of the file (kind `pie`, `PT_INTERP`
  `/lib64/ld-linux-x86-64.so.2`, `DT_NEEDED libc.so.6`, `NoTextRelD`), from the per-part reader's
  checked parse and the `noTextRel` check;
* `hello_cli`: **the row `silmaril.elf.cli.hello.gcc_o2`**: those facts, and `Std.hello` under
  `glibcStream`, from `helloGcc_prints` (`Program.Verified` read in the CLI institution).

What this rests on is the model's trust base (`Silmaril.Elf.CliExe.Glibc.Defs`): the executable's
code runs on `Open9` from its entry `_start`; glibc (`__libc_start_main`, `puts`, `exit`,
`__cxa_finalize`) is trusted as one atomic contract step each, and the loader as the `Dyn.Loader`
relation. That glibc's code meets those contracts is the open problem `HelloLib` of
`Silmaril.Elf.Link.Dyn.LibMod.Hello` (`helloGcc_real`).
-/

@[expose] public section

namespace Silmaril.Elf.CliExe.Hello

open Silmaril.Elf

theorem helloOk : CliExe.ExeOk (blobOf helloGcc.bytes) .pie .glibcDyn :=
  Silmaril.Proofs.Elf.CliExe.Hello.helloOk

/-- **`hello-gcc` is a CLI executable printing `hello, world`.** -/
@[solves "silmaril.elf.cli.hello.gcc_o2"]
theorem hello_cli : silmaril.elf.cli.hello.gcc_o2 :=
  ⟨helloOk, Silmaril.Proofs.Elf.CliExe.Hello.hello_stream⟩

end Silmaril.Elf.CliExe.Hello

silmaril group silmaril.elf.cli
  (title := "ELF executables as CLI programs: the cli_exe shape and its rows")
  (children := [silmaril.shapes.elf.cli_exe, silmaril.shapes.elf.cli_exe.glibc,
    silmaril.shapes.elf.cli_exe.static, silmaril.elf.cli.hello.gcc_o2])
