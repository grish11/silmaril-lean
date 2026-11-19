module
public import Silmaril.Elf.Corpus.CjsonTypePredicates.Source.Elaboration.Defs
namespace Silmaril.Proofs.Elf.Corpus.CjsonTypePredicates
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
set_option cbv.maxSteps 4000000
attribute [local cbv_eval] Silmaril.Cerberus.Elaboration.Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton
public theorem layout_checked :
    Silmaril.Elf.Corpus.CjsonTypePredicates.Source.Elaboration.layoutSignature =
      some (64, 8, some 24) := by cbv
end Silmaril.Proofs.Elf.Corpus.CjsonTypePredicates
