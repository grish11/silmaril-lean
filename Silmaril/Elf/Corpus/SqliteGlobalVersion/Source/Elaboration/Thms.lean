module
public import Silmaril.Elf.Corpus.SqliteGlobalVersion.Source.Elaboration.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteGlobalVersion.Bindings
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteGlobalVersion.Source.Elaboration
theorem actual_exists : actual.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.SqliteGlobalVersion.actual_exists
def function : Silmaril.Project.Shapes.C.CFn Source.signature where
  file := core.toFile
  params := []
  body := (actual.get actual_exists).2.2.2
end Silmaril.Elf.Corpus.SqliteGlobalVersion.Source.Elaboration
