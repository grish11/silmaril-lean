module

public import Silmaril.Elf.LpsCli.Defs
public import Silmaril.Cli.Institution.Std.Defs
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Elf
public import Silmaril.Process.LPS.Problems.Sha256Cli.Elf
public import Silmaril.Process.CLI.Sha256

/-!
# The static sha256 executables as models of the CLI institution (level `L1`)

Two pinned static x86-64 executables have end-to-end LPS proofs in `Silmaril.Process.LPS`:

* **`sha256sum-min`** (`GnuSha256sum.file`, 35512 bytes, SHA-256 `22fa6345…d42817`): a static,
  libc-free x86-64 reimplementation of every option of GNU coreutils 9.4 `sha256sum` (gcc 13.3.0
  `-O2` driver, clang `-O2` compression function). It is *not* linked against musl: it has its
  own `_start` and issues its system calls directly. `staticModel` is its `L1` model
  (`lpsModel` over `ext8`).
* **the `sha256` filter** (`Sha256Cli.file`, 2368 bytes, SHA-256 `6eaae149…89e1f7`): a
  freestanding filter printing `hex(SHA-256(stdin)) ++ "\n"`. `filterModel` is its `L1` model
  (`lpsModel` over `ext`), and `hexLine` its sentence's function.

`Thms`: both meet their sentences unconditionally; `sha256sum-min` meets the **same** standard
sentence as the real GNU `sha256sum` on glibc (`Std.sha256Stdin`), so the two agree run by run;
the two sentences are related by `"\n" ↦ "  -\n"` on the last line.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Elf.LpsCli.Sha256sum

open Silmaril.Process.LPS.Problems
open Silmaril.Cli.Institution (Level Model Sen)

/-- **`sha256sum-min` under LPS** (`L1`). -/
def staticModel : Model Level.stream.sig := lpsModel GnuSha256sum.file ext8

/-- The `sha256` filter's output: 64 lower-case hex digits and `"\n"`. -/
def hexLine (s : Silmaril.Cli.Bytes) : Silmaril.Cli.Bytes :=
  cliBytes (Silmaril.Process.CLI.Sha256.expected (lpsBytes s))

/-- **The `sha256` filter under LPS** (`L1`). -/
def filterModel : Model Level.stream.sig := lpsModel Sha256Cli.file ext

end Silmaril.Elf.LpsCli.Sha256sum
