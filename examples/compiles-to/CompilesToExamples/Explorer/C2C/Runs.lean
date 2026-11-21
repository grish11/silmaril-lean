module

-- The Core dynamics reads source locations through `String.splitOn`; these imports expose the
-- String bodies so that `cbv` can run the Core (as in the generated canonical-safety proofs).
import all Init.Data.String.Legacy
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
public import CompilesToExamples.Explorer.C2C.Defs
public import CompilesToExamples.Straight.Defs
public import Silmaril.Project.Shapes.CompilesTo.Translate.Thms

/-!
# C ⇒ C translations of `add3`: evaluated runs and refutations

Each function's Core, from its canonical entry with the arguments `1, 2, 3`, has a forced run
(every state one successor) halting with a defined integer; `cbv` evaluates it and the kernel
checks the evaluation:

| function | `add3(1, 2, 3)` |
| --- | --- |
| `CompilesToExamples.Straight.add3Fn` | 6 |
| `add3ReassocFn` | 6 |
| `add3DoubleFn` | 12 |
| `add3OperandFn` | 4 |
| `add3DropFn` | 3 |

The three buggy translations are refuted (`¬ CanonicalRefines add3Fn _`): the doubled
result, the wrong operand and the dropped operand. `add3_reassoc` agrees on this tuple; its
equivalence (every tuple) is not proved. `add3_op` (`s - c`) is not decided: its Core run is not
evaluated here, so its status stays unknown.
-/

namespace CompilesToExamples.Explorer.C2C

open Silmaril.Project.CompilesTo
open Silmaril.Project.Shapes.CompilesTo
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

attribute [local cbv_eval] Silmaril.Cerberus.Core.Dynamics.requestAux.eq_def
attribute [local cbv_eval] Silmaril.Cerberus.Core.Dynamics.hasCCall.eq_def
attribute [local cbv_eval] Silmaril.Cerberus.Core.Dynamics.controlHasCCall.eq_def
attribute [local cbv_eval] Silmaril.Cerberus.Core.Dynamics.activeCall.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton

/-- The arguments `1, 2, 3`. -/
@[expose] public def args123 : Silmaril.X86.SystemV.CApi.Arguments [.int32, .int32, .int32] :=
  .cons (kind := .int32) (1 : BitVec 32) (.cons (kind := .int32) (2 : BitVec 32)
    (.cons (kind := .int32) (3 : BitVec 32) .nil))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem source_run : endsInt 6 (forcedRun CompilesToExamples.Straight.add3Fn.file CompilesToExamples.Straight.add3Fn.labels 400
    (CompilesToExamples.Straight.add3Fn.canonicalEntry args123)) = true := by
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem reassoc_run : endsInt 6 (forcedRun add3ReassocFn.file add3ReassocFn.labels 400
    (add3ReassocFn.canonicalEntry args123)) = true := by
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem double_run : endsInt 12 (forcedRun add3DoubleFn.file add3DoubleFn.labels 1000
    (add3DoubleFn.canonicalEntry args123)) = true := by
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem operand_run : endsInt 4 (forcedRun add3OperandFn.file add3OperandFn.labels 400
    (add3OperandFn.canonicalEntry args123)) = true := by
  cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem drop_run : endsInt 3 (forcedRun add3DropFn.file add3DropFn.labels 400
    (add3DropFn.canonicalEntry args123)) = true := by
  cbv

/-- **Refuted**: `add3DoubleFn` is not a translation of `add3` (on `add3(1, 2, 3)` it returns 12, `add3`
returns 6). -/
public theorem double_refuted : ¬ CanonicalRefines CompilesToExamples.Straight.add3Fn add3DoubleFn :=
  CanonicalRefines.refuted_of_ends _ _ args123 source_run double_run (by decide)

/-- **Refuted**: `add3OperandFn` is not a translation of `add3` (on `add3(1, 2, 3)` it returns 4, `add3`
returns 6). -/
public theorem operand_refuted : ¬ CanonicalRefines CompilesToExamples.Straight.add3Fn add3OperandFn :=
  CanonicalRefines.refuted_of_ends _ _ args123 source_run operand_run (by decide)

/-- **Refuted**: `add3DropFn` is not a translation of `add3` (on `add3(1, 2, 3)` it returns 3, `add3`
returns 6). -/
public theorem drop_refuted : ¬ CanonicalRefines CompilesToExamples.Straight.add3Fn add3DropFn :=
  CanonicalRefines.refuted_of_ends _ _ args123 source_run drop_run (by decide)

end CompilesToExamples.Explorer.C2C
