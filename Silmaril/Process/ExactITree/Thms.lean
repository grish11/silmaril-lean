module

public import Silmaril.Process.ExactITree.Defs
public import Silmaril.Semantics.ExactITree.Thms
import Silmaril.Proofs.Process.ExactITree.File

/-! Checked satisfaction and failure for the positioned-read fixture. -/

public section

namespace Silmaril.Process.ExactITree.File

open Silmaril.Elgot.ITree.Exact

/-- The positioned call leaves the cursor at zero for the following read. -/
theorem correct_finished (log : List UInt8) (last : End profile ReadPair) :
    Observes (kernel false) contents ((sentence.lower lowering).test, 0) (.finished log last) ↔
      log = [] ∧ last = .returned (some 0x42, some 0x41) 1 :=
  Proofs.correct_finished log last

/-- Replacing the positioned operation with a cursor read consumes both bytes in order. -/
theorem swapped_finished (log : List UInt8) (last : End profile ReadPair) :
    Observes (kernel true) contents ((sentence.lower lowering).test, 0) (.finished log last) ↔
      log = [] ∧ last = .returned (some 0x41, some 0x42) 2 :=
  Proofs.swapped_finished log last

theorem correct_target : Satisfies (kernel false) (sentence.lower lowering) :=
  Proofs.correct_target

theorem correct_source : Satisfies (Kernel.reduct lowering (kernel false)) sentence :=
  (satisfies_lower lowering _ sentence).mp correct_target

theorem swapped_target : ¬ Satisfies (kernel true) (sentence.lower lowering) :=
  Proofs.swapped_target

theorem swapped_source : ¬ Satisfies (Kernel.reduct lowering (kernel true)) sentence :=
  fun h => swapped_target ((satisfies_lower lowering _ sentence).mpr h)

end Silmaril.Process.ExactITree.File
