module

public import Silmaril.Elf.Corpus.MimallocVersion.Source.Core.Defs

namespace Silmaril.Proofs.Elf.Corpus.MimallocVersion.SourceCore
open Silmaril.Elf.Corpus.MimallocVersion.Source.Core
open Silmaril.Project.Shapes.C

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

attribute [local cbv_eval] Silmaril.Cerberus.Elaboration.Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton

public theorem elab_eq : ElabAil ail = .ok core := by cbv

public theorem elaborates : Task.elaborates :=
  ⟨core, elab_eq, rfl, _, _, _, _, rfl, _, rfl, rfl⟩

end Silmaril.Proofs.Elf.Corpus.MimallocVersion.SourceCore
