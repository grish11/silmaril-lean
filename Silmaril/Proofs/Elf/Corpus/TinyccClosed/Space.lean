module
public import Silmaril.Elf.Corpus.TinyccClosed.Space.Defs
namespace Silmaril.Proofs.Elf.Corpus.TinyccClosed.Space
open Silmaril.Elf.Corpus.TinyccClosed.Space
open Silmaril.Project.Shapes.C
set_option maxRecDepth 32768
set_option maxHeartbeats 32000000
attribute [local cbv_eval] Silmaril.Cerberus.Elaboration.Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton
public theorem elab_eq : ElabAil ail = .ok core := by cbv
public theorem elaborates : ElaboratesTo ail "is_space" sourceFn :=
  ⟨core, elab_eq, rfl, _, _, _, _, rfl, _, rfl, rfl⟩
end Silmaril.Proofs.Elf.Corpus.TinyccClosed.Space
