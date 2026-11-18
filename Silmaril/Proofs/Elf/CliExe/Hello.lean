module

public import Silmaril.Elf.CliExe.Hello.Defs
public import Silmaril.Elf.CliExe.Glibc.Thms
public import Silmaril.Elf.Exe.Thms
public import Silmaril.Elf.Staged.Pinned.HelloGcc.Thms
public import Silmaril.Elf.Link.Dyn.Program.Cli.Examples
public import Silmaril.Elf.Link.Dyn.Program.Examples.Thms
public import Silmaril.Project.Shapes.Elf.Thms

/-! # Proofs of `Silmaril.Elf.CliExe.Hello`

Ported from hiloopai/moria-lean (`2c7713d157`) `Moria/Project/Shapes/ElfExe/Thms.lean` (`helloOk`,
`hello_cli`) and `Moria/Project/Cli/Bench/Thms.lean` (`hello_file`, `hello_gcc_o2`). The ELF API
facts come from the per-part reader's parse of the same file (`Silmaril.Elf.Staged.Pinned.HelloGcc`)
instead of moria's `Exe.Examples.helloGcc_meta`. -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.CliExe.Hello

open Silmaril.Elf Silmaril.Elf.CliExe
open Silmaril.Elf.Link.Dyn.Program (libc ld)

/-- The Program API's description of `hello-gcc` describes the row's file. -/
theorem hello_file :
    Silmaril.Elf.Link.Dyn.Program.Examples.helloGcc.file = blobOf Hello.helloGcc.bytes :=
  (Silmaril.Project.Shapes.blob_of_decode rfl rfl).symm

/-- The per-part reader's file is the row's file (the same `include_bytes` file). -/
theorem reader_file : Silmaril.Elf.Staged.Pinned.HelloGcc.F = blobOf Hello.helloGcc.bytes := rfl

/-- **`hello-gcc`'s glibc facts**: a PIE, interpreted by `ld-linux`, needing `libc.so.6`, with no
loader write on a read-only segment. -/
theorem helloOk : CliExe.ExeOk (blobOf Hello.helloGcc.bytes) .pie .glibcDyn := by
  rw [← reader_file]
  have hp := Silmaril.Elf.Staged.Pinned.HelloGcc.parses
  refine ⟨⟨_, hp, by decide⟩, rfl, ⟨_, hp, by decide⟩, ⟨_, ⟨_, hp, rfl⟩, by decide⟩, ?_⟩
  rw [reader_file, ← hello_file]
  exact Silmaril.Elf.Exe.noTextRelD_of_check (by decide +kernel)

theorem helloBytes_eq :
    Silmaril.Cli.Institution.Std.helloBytes = Silmaril.Elf.Link.Dyn.Program.lit "hello, world\n" := by
  decide +kernel

/-- **`hello-gcc` prints `hello, world` and exits 0 under `glibcStream`.** -/
theorem hello_stream : (glibcStream Hello.helloGcc.bytes).Sat Silmaril.Cli.Institution.Std.hello := by
  have h := (Silmaril.Elf.Link.Dyn.Program.Examples.helloGcc_prints .cwd).mono
    (Silmaril.Cli.Institution.Level.liftAll_le_lift _)
  rw [Silmaril.Cli.Institution.Std.hello, helloBytes_eq]
  exact glibcStream_sat hello_file Silmaril.Elf.Link.Dyn.Program.Examples.helloGcc_ok h

end Silmaril.Proofs.Elf.CliExe.Hello
