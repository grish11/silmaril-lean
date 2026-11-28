module

import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers

open RVSDG (Origin Port Tuple)
open Memory.Forwarding.Disjoint (Certificate)

private abbrev args : List ValueSort := [.address, .address, .word, .word]

private def observed : Port args .address := .head
private def reader : Port args .address := .tail .head
private def early : Port args .word := .tail (.tail .head)
private def late : Port args .word := .tail (.tail (.tail .head))

private def middle : Origin args [[.word], [.word], [.word]] .word := .output (1 : Fin 3) .head

private def source : Graph args :=
  .load (.latest 0) (.arg observed)
    (.store (.latest 0) (.arg observed) (.arg early)
      (.load (.latest 1) (.arg reader)
        (.store (.latest 1) (.arg observed) (.arg late)
          (.load (.latest 2) (.arg observed) (.ret (.latest 2) middle)))))

private def target : Graph args :=
  .load (.latest 0) (.arg observed)
    (.load (.latest 0) (.arg reader)
      (.store (.latest 0) (.arg observed) (.arg late)
        (.load (.latest 1) (.arg observed) (.ret (.latest 1) middle))))

private def facts : Certificate args := ⟨observed, [reader]⟩
private def chosen : Selection.Result args := ⟨⟨1, 2⟩, facts, target⟩

private def input (cell : Address 3) : Tuple (Val 3) args :=
  .cons (0 : Address 3) (.cons cell (.cons (8 : Word) (.cons (11 : Word) .nil)))

private def initial : Heap 3 := fun address => if address = 1 then 4 else 1
private def final : Heap 3 := initial.write 0 11

-- Both outside Loads read the overwritten cell and stay in order.
-- Only the Load between the two Stores contributes a reader obligation.
example : discover source 1 = some facts := rfl
private theorem selected : rewrite source (input 1) = some chosen := rfl
example : Selection.rewrite source [facts] (input 1) = some chosen := rfl

/-- info: some (1, 2) -/
#guard_msgs in
#eval (rewrite source (input 1)).map fun result =>
  (result.candidate.removeVersion, result.candidate.overwriteVersion)

example : source.Returns (input 1) initial 4 final :=
  (rewrite_returns_iff (input 1) selected initial 4 final).mp
    ((target.returns_iff_denote (input 1) initial 4 final).mpr (by cbv))

-- The same certificate is inferred, but validation rejects the distinct
-- reader port when it resolves to the very cell written by the Stores.
example : rewrite source (input 0) = none := rfl
example : source.denote (input 0) initial = (8, final) := by
  cbv
  simp only [final, Heap.write, Function.update_idem]
example : target.denote (input 0) initial = (1, final) := by cbv

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers
