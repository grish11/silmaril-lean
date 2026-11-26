module

import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat

open RVSDG (Origin Port Tuple)
open Silmaril.MLIR.MemRef (Buffer)

private abbrev args : List ValueSort := [.address, .address, .word, .word]

private def x : Port args .address := .head
private def y : Port args .address := .tail .head
private def early : Port args .word := .tail (.tail .head)
private def late : Port args .word := .tail (.tail (.tail .head))
private def loaded : Origin args [[.word]] .word := .output (0 : Fin 1) .head

private def source : Graph args :=
  .store (.latest 0) (.arg x) (.arg early)
    (.load (.latest 1) (.arg y)
      (.store (.latest 1) (.arg x) (.arg late)
        (.store (.latest 2) (.arg y) (.arg early)
          (.store (.latest 3) (.arg y) (.arg late) (.ret (.latest 4) loaded)))))

private def disjointTarget : Graph args :=
  .load (.latest 0) (.arg y)
    (.store (.latest 0) (.arg x) (.arg late)
      (.store (.latest 1) (.arg y) (.arg late) (.ret (.latest 2) loaded)))

private def aliasTarget : Graph args :=
  .store (.latest 0) (.arg x) (.arg early)
    (.load (.latest 1) (.arg y)
      (.store (.latest 1) (.arg x) (.arg late)
        (.store (.latest 2) (.arg y) (.arg late) (.ret (.latest 3) loaded))))

private def input (yCell : Address 3) : Tuple (Val 3) args :=
  .cons (0 : Address 3) (.cons yCell (.cons (8 : Word) (.cons (11 : Word) .nil)))

private def initial : Heap 3 := fun address => if address = 1 then 4 else 1
private def disjointHeap : Heap 3 := (initial.write 0 11).write 1 11
private def aliasHeap : Heap 3 := initial.write 0 11

-- With distinct cells the scan succeeds twice, including after renumbering.
example : rewrite source (input 1) = ⟨disjointTarget, 2⟩ := rfl
example : ((Readers.rewrite source (input 1)).bind
    (fun first => Readers.rewrite first.graph (input 1))).map
    (fun second => (second.candidate.removeVersion, second.candidate.overwriteVersion)) =
      some (2, 3) := rfl
example : (Readers.rewrite (rewrite source (input 1)).graph (input 1)).isNone = true := rfl
example : rewrite disjointTarget (input 1) = ⟨disjointTarget, 0⟩ := rfl
example : source.denote (input 1) initial = (4, disjointHeap) :=
  (rewrite_denote source (input 1) initial).symm.trans (by cbv)

-- Aliasing protects the first Store because the Load reads its word.
-- The unrelated candidate on the original y wire still deletes one Store.
example : rewrite source (input 0) = ⟨aliasTarget, 1⟩ := rfl
example : (Readers.rewrite aliasTarget (input 0)).isNone = true := rfl
example : source.denote (input 0) initial = (8, aliasHeap) := by
  rw [← rewrite_denote source (input 0) initial]
  cbv
  simp only [aliasHeap, Heap.write, Function.update_idem]

/-- info: (2, true, 1) -/
#guard_msgs in
#eval
  let disjoint := rewrite source (input 1)
  (disjoint.deleted, (Readers.rewrite disjoint.graph (input 1)).isNone,
    (rewrite source (input 0)).deleted)

private def readback (result : Word × Buffer 3) : List Word :=
  result.1 :: (List.finRange 3).map result.2.cell

private def memrefComparison (yCell : Address 3) : Nat × List Word × List Word :=
  let lowered := MemRef.lower source (input yCell)
  (lowered.deleted, readback (lowered.runOriginal ⟨initial⟩),
    readback (lowered.runOptimized ⟨initial⟩))

-- Each list contains the returned word followed by every buffer cell.
/-- info: (2, [4#64, 11#64, 11#64, 1#64], [4#64, 11#64, 11#64, 1#64]) -/
#guard_msgs in
#eval memrefComparison 1

/-- info: (1, [8#64, 11#64, 4#64, 1#64], [8#64, 11#64, 4#64, 1#64]) -/
#guard_msgs in
#eval memrefComparison 0

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat
