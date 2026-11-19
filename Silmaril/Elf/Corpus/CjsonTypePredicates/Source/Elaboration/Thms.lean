module
public import Silmaril.Elf.Corpus.CjsonTypePredicates.Source.Elaboration.Defs
import Silmaril.Proofs.Elf.Corpus.CjsonTypePredicates.RunResult
import Silmaril.Proofs.Elf.Corpus.CjsonTypePredicates.Layout
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonTypePredicates.Source.Elaboration
/-- The Core selected with the checked success witness is the actual result. -/
theorem run_eq_core : Source.inputs.run Source.ail = .ok core :=
  Silmaril.Proofs.Elf.Corpus.CjsonTypePredicates.run_eq_core
theorem layout_checked : layoutSignature = some (64, 8, some 24) :=
  Silmaril.Proofs.Elf.Corpus.CjsonTypePredicates.layout_checked
end Silmaril.Elf.Corpus.CjsonTypePredicates.Source.Elaboration
