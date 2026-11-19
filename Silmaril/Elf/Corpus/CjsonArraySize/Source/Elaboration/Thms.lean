module
public import Silmaril.Elf.Corpus.CjsonArraySize.Source.Elaboration.Defs
import Silmaril.Proofs.Elf.Corpus.CjsonArraySize.Bindings
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArraySize.Source.Elaboration
theorem actual_exists : actual.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.CjsonArraySize.actual_exists
def actualData := actual.get actual_exists
def function : Silmaril.Project.Shapes.C.CFn Source.signature where
  file := core.toFile
  params := actualData.1
  body := actualData.2
end Silmaril.Elf.Corpus.CjsonArraySize.Source.Elaboration
