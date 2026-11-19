module
public import Silmaril.Elf.Corpus.CjsonInsert.Source.Defs
set_option cbv.maxSteps 8000000
namespace Silmaril.Proofs.Elf.Corpus.CjsonInsert
open Silmaril.Elf.Corpus.CjsonInsert
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
attribute [local cbv_eval] Silmaril.Cerberus.Elaboration.Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton
public theorem succeeds : (Source.inputs.run Source.ail).toOption.isSome = true := by
  cbv
end Silmaril.Proofs.Elf.Corpus.CjsonInsert
