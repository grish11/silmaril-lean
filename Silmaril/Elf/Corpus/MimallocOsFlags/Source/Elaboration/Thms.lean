module
public import Silmaril.Elf.Corpus.MimallocOsFlags.Source.Elaboration.Defs
import Silmaril.Proofs.Elf.Corpus.MimallocOsFlags.RunResult
import Silmaril.Proofs.Elf.Corpus.MimallocOsFlags.Bindings
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocOsFlags.Source.Elaboration
theorem run_eq_core : Source.inputs.run Source.ail = .ok core :=
  Silmaril.Proofs.Elf.Corpus.MimallocOsFlags.run_eq_core
theorem body_exists (g : Getter) : (actualBody g).isSome = true :=
  Silmaril.Proofs.Elf.Corpus.MimallocOsFlags.actual_bodies g
/-- Body selected from the actual Core only after checked procedure/ABI lookup. -/
def function (g : Getter) : Silmaril.Project.Shapes.C.CFn Source.signature where
  file := core.toFile
  params := []
  body := (actualBody g).get (body_exists g)
end Silmaril.Elf.Corpus.MimallocOsFlags.Source.Elaboration
