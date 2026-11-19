module
public import Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Source.Elaboration.Defs
namespace Silmaril.Proofs.Elf.Corpus.DarkhttpdLogEncoding
open Silmaril.Elf.Corpus.DarkhttpdLogEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
set_option cbv.maxSteps 4000000
attribute [local cbv_eval] Silmaril.Cerberus.Elaboration.Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton
public theorem actual_exists : Source.Elaboration.actual.isSome = true := by cbv
end Silmaril.Proofs.Elf.Corpus.DarkhttpdLogEncoding
