module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.CaptureDemand.Thms

/-! Backward capture demand on a cycle with an independent exit row. -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand.Examples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic

-- The second row reads slot zero in its jump argument. The first row
-- must carry that slot even though it has no direct reads. The third row
-- reads slot one and is outside the cycle. These are ambient named reads.
private def fixture (param : Nat) : CFG Nat Nat Empty :=
  ⟨.term (.br 10 .unit),
    [(10, ⟨param, .term (.br 20 .unit)⟩),
     (20, ⟨3, .term (.br 10 (.var 0))⟩),
     (30, ⟨3, .term (.br 99 (.var 1))⟩)]⟩

private def names (slot : Fin 2) : Nat := slot.val

example : List.ofFn (direct (fixture 3) names) = [∅, {0}, {1}] := by decide
example : List.ofFn (infer (fixture 3) names) = [{0}, {0}, {1}] := by decide
example : List.ofFn (ordered (fixture 3) names [1, 0]) = [[0], [0], [1]] := by decide

-- The current compiler installs both support registers even at the first
-- row, where the least closed capture plan requests only register zero.
example : Versioning.slots (fixture 3) (fixture 3).blocks[0].2 = [0, 1] := by decide

-- Changing the first parameter to register zero kills the caller value.
-- Every plan closed under the cycle still needs it at that row.
example : ¬ ∃ live, Closed (fixture 0) names live ∧ NoShadow (fixture 0) names live := by
  rw [noShadow_iff]
  intro valid
  exact valid ⟨0, by decide⟩ 0 (by decide) rfl

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand.Examples
