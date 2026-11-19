module
public import Silmaril.Elf.Corpus.SqliteGlobalVersion.Source.Elaboration.Defs
namespace Silmaril.Proofs.Elf.Corpus.SqliteGlobalVersion
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
set_option cbv.maxSteps 4000000
attribute [local cbv_eval] Silmaril.Cerberus.Elaboration.Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton
public theorem actual_exists :
    Silmaril.Elf.Corpus.SqliteGlobalVersion.Source.Elaboration.actual.isSome = true := by
  cbv
end Silmaril.Proofs.Elf.Corpus.SqliteGlobalVersion
