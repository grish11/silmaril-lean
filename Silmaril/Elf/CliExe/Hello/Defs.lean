module

public import Silmaril.Elf.CliExe.Glibc.Defs
public import Silmaril.Elf.Link.Dyn.Pin.Bytes
public import Silmaril.Cli.Institution.Std.Defs

/-! # `hello-gcc` as a CLI executable: the row

`silmaril.elf.cli.hello.gcc_o2`, a row of `silmaril.shapes.elf.cli_exe`: the pinned `hello-gcc`
(`examples/dyn/pinned/hello-gcc`, gcc 13.3 `-O2`, PIE, dynamically linked against glibc 2.39) is
an executable of kind `pie`, interpreted by `/lib64/ld-linux-x86-64.so.2`, needing `libc.so.6`,
with no loader write on a read-only segment, and under the glibc model at `L1`
(`CliExe.glibcStream`) it satisfies the standard sentence `Std.hello` (stdout is
`hello, world\n`, exit status 0). Proved in `Thms` (`hello_cli`).

Ported from hiloopai/moria-lean (`2c7713d157`) `Moria/Project/Shapes/ElfExe/Defs.lean`
(`moria.elf.cli.hello.gcc_o2`), on silmaril's `cli_exe` shape; the bench's other rows (other
compilers and flags, musl, GNU `sha256sum`, coreutils) stay in moria-lean.
-/

@[expose] public section

namespace Silmaril.Elf.CliExe.Hello

/-- `hello-gcc` as a value of `elf.ast` (its bytes: `Silmaril.Elf.Link.Dyn.PinBytes.helloGcc`). -/
noncomputable def helloGcc : Silmaril.Project.Value Silmaril.Elf.File :=
  ⟨Silmaril.Elf.format, Silmaril.Elf.Link.Dyn.PinBytes.helloGcc⟩

end Silmaril.Elf.CliExe.Hello

end

silmaril instance silmaril.elf.cli.hello.gcc_o2
    (title := "hello-gcc (glibc 2.39, PIE) prints hello, world and exits 0, under the glibc process model") :=
  silmaril.shapes.elf.cli_exe (exe := Silmaril.Elf.CliExe.Hello.helloGcc) (k := Silmaril.Elf.Kind.pie)
  (ld := Silmaril.Elf.CliExe.Loading.glibcDyn) (L := Silmaril.Cli.Institution.Level.stream)
  (M := Silmaril.Elf.CliExe.glibcStream) (φ := Silmaril.Cli.Institution.Std.hello)
