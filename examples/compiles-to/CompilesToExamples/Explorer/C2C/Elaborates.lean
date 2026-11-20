module

public import CompilesToExamples.Explorer.C2C.Defs
import all Init.Data.List.Sort.Basic

namespace CompilesToExamples.Explorer.C2C

open Silmaril.Project.Shapes.C (ElabAil)

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

attribute [local cbv_eval] Silmaril.Cerberus.Elaboration.Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort.eq_3 List.mergeSort_nil List.mergeSort_singleton

/-- The exact typed Ail of `translations.c` elaborates to the Core used by its models. -/
public theorem elab_eq : ElabAil ail = .ok core := by cbv

end CompilesToExamples.Explorer.C2C
