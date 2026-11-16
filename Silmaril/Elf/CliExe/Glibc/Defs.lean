module

public import Silmaril.Elf.CliExe.Defs
public import Silmaril.Elf.Link.Dyn.Program.Cli.Defs
public import Silmaril.Elf.Link.Dyn.Program.Glibc

/-! # CLI models of a dynamically linked executable on glibc

Models for `silmaril.shapes.elf.cli_exe` with `ld := .glibcDyn` (`M : Bytes → Model L.sig`), from
the Program API's process model (`Silmaril.Elf.Link.Dyn.Program.x86Model`). Ported from
hiloopai/moria-lean (`2c7713d157`) `Moria/Project/Cli/Defs.lean` (`glibcPin`, `glibcStream`),
restated as models of the bytes, as silmaril's `cli_exe` takes them; moria's `CliModel` wrapper
and its other models (WASI, simulators, the coreutils and GNU `sha256sum` models) stay there.

* `glibcPin pc pl env conv b` (`L3`): a run of the file `b` is a run that **every** checked
  description `B` of it allows (`B.file = blobOf b` and the per-binary check `B.ok pc pl`), in the
  process model on any `libc.so.6`/`ld.so` agreeing with the lookup pins `pc`/`pl`. With no checked
  description every run is allowed, so a sentence holds only through a description that passes the
  check (`glibcPin_sat`, `Thms`), never by an empty model.
* `glibcStream b` (`L1`): `glibcPin` on the pinned glibc 2.39 (`Program.libc`, `Program.ld`), read at
  `L1` by the default expansion of the input (`Level.reduct`, through `Level.hom .stream .full`).

**Trusted** (as for `x86Model` and `Program.Verified`): the `Open9` instruction semantics of the
executable's code, the loader relation (`Dyn.Loader`, a transcription of `ld.so`), glibc's functions
as one atomic step each with the contracts of `Silmaril.Elf.Link.Dyn.Proc` (`__libc_start_main`,
`puts`, `exit`, `__cxa_finalize`, the lazy resolver), and the reading of an invocation as a world
(`worldOf`). glibc's own code is not executed.
-/

@[expose] public section

namespace Silmaril.Elf.CliExe

open Silmaril.Cli.Institution (Level Model)
open Silmaril.Elf.Link.Dyn.Program (Bin LibPin Std PathConv x86Model lib)

/-- **The glibc process model over lookup pins** (`L3`, module doc). -/
def glibcPin (pc pl : LibPin) (env : Std → Prop := fun _ => True) (conv : PathConv := .cwd)
    (b : Silmaril.Formats.Bytes) : Model Level.full.sig :=
  ⟨fun i o => ∀ B : Bin, B.file = blobOf b → B.ok pc pl = true →
    (x86Model B pc pl lib env conv).Run i o⟩

/-- **The glibc model at `L1`**: `glibcPin` on the pinned glibc 2.39, read at `L1`. -/
def glibcStream (b : Silmaril.Formats.Bytes) : Model Level.stream.sig :=
  Level.stream.reduct
    (glibcPin Silmaril.Elf.Link.Dyn.Program.libc Silmaril.Elf.Link.Dyn.Program.ld (b := b))

end Silmaril.Elf.CliExe
