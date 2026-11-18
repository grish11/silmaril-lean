module

public import Silmaril.Elf.CliExe.Glibc.Defs
public import Silmaril.Cli.Institution.Thms

/-! # The glibc CLI models: satisfaction through a checked description

* `glibcPin_sat`: a sentence the process model of one checked description satisfies holds in
  `glibcPin`;
* `glibcStream_sat`: an `L1` sentence whose lift (default expansion) such a description satisfies
  holds in `glibcStream`.
-/

@[expose] public section

namespace Silmaril.Elf.CliExe

open Silmaril.Cli.Institution (Level Model Sen)
open Silmaril.Elf.Link.Dyn.Program (Bin LibPin Std PathConv x86Model lib)

theorem glibcPin_sat {pc pl : LibPin} {env : Std → Prop} {conv : PathConv}
    {b : Silmaril.Formats.Bytes} {B : Bin} (hf : B.file = blobOf b) (hok : B.ok pc pl = true)
    {φ : Silmaril.Cli.Institution.Sen Level.full.sig} (h : (x86Model B pc pl lib env conv).Sat φ) :
    (glibcPin pc pl env conv b).Sat φ :=
  fun i o hr => h i o (hr B hf hok)

theorem glibcStream_sat {b : Silmaril.Formats.Bytes} {B : Bin} (hf : B.file = blobOf b)
    (hok : B.ok Silmaril.Elf.Link.Dyn.Program.libc Silmaril.Elf.Link.Dyn.Program.ld = true)
    {φ : Sen Level.stream.sig}
    (h : (x86Model B Silmaril.Elf.Link.Dyn.Program.libc Silmaril.Elf.Link.Dyn.Program.ld).Sat
      (Level.lift φ)) : (glibcStream b).Sat φ :=
  (Level.sat_lift_iff _ φ).mp (glibcPin_sat hf hok h)

end Silmaril.Elf.CliExe
