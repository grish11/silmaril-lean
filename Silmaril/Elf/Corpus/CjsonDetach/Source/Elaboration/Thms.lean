module
public import Silmaril.Elf.Corpus.CjsonDetach.Source.Elaboration.Defs
import Silmaril.Proofs.Elf.Corpus.CjsonDetach.Bindings
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonDetach.Source.Elaboration
theorem actual_exists : actual.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.CjsonDetach.actual_exists
def actualData := actual.get actual_exists
def function : Silmaril.Project.Shapes.C.CFn Source.signature where
  file := core.toFile
  params := actualData.1
  body := actualData.2
end Silmaril.Elf.Corpus.CjsonDetach.Source.Elaboration
