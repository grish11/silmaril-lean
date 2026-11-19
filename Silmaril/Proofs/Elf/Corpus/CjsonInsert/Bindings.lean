module
public import Silmaril.Elf.Corpus.CjsonInsert.Source.Elaboration.Defs
namespace Silmaril.Proofs.Elf.Corpus.CjsonInsert
open Silmaril.Elf.Corpus.CjsonInsert
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
set_option cbv.maxSteps 8000000
attribute [local cbv_eval] Silmaril.Cerberus.Elaboration.Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton
private theorem mergeSort_four {α : Type} (a b c d : α) (le : α → α → Bool) :
    [a,b,c,d].mergeSort le = List.merge ([a,b].mergeSort le) ([c,d].mergeSort le) le := by
  exact List.mergeSort_append [a,b] [c,d] (by simp) (by simp)
attribute [local cbv_eval] mergeSort_four List.cons_merge_cons List.nil_merge List.merge_right
public theorem actual_exists : Source.Elaboration.actual.isSome = true := by cbv
end Silmaril.Proofs.Elf.Corpus.CjsonInsert
