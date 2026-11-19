module
public import Silmaril.Elf.Corpus.CjsonArrayItem.Source.Elaboration.Defs
import Silmaril.Proofs.Elf.Corpus.CjsonArrayItem.Bindings
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArrayItem.Source.Elaboration
theorem actual_exists : actual.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.CjsonArrayItem.actual_exists
def actualData := actual.get actual_exists
def function : Silmaril.Project.Shapes.C.CFn Source.signature where
  file := core.toFile
  params := actualData.1
  body := actualData.2
end Silmaril.Elf.Corpus.CjsonArrayItem.Source.Elaboration
