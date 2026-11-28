module

import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection

open RVSDG (Origin Port Tuple)
open Memory.Forwarding.Disjoint (Certificate)

private abbrev args : List ValueSort := [.address, .address, .word, .word]

private def headPort : Port args .address := .head
private def sidePort : Port args .address := .tail .head
private def early : Port args .word := .tail (.tail .head)
private def late : Port args .word := .tail (.tail (.tail .head))

private def loaded : Origin args [[.word]] .word := .output (0 : Fin 1) .head

private def source (reader : Port args .address := sidePort) : Graph args :=
  .store (.latest 0) (.arg headPort) (.arg early)
    (.load (.latest 1) (.arg reader)
      (.store (.latest 1) (.arg headPort) (.arg late)
        (.store (.latest 2) (.arg sidePort) (.arg early)
          (.store (.latest 3) (.arg sidePort) (.arg late) (.ret (.latest 4) loaded)))))

private def target : Graph args :=
  .load (.latest 0) (.arg sidePort)
    (.store (.latest 0) (.arg headPort) (.arg late)
      (.store (.latest 1) (.arg sidePort) (.arg early)
        (.store (.latest 2) (.arg sidePort) (.arg late) (.ret (.latest 3) loaded))))

private def headFacts : Certificate args := ⟨headPort, [sidePort]⟩
private def sideFacts : Certificate args := ⟨sidePort, []⟩
private def certificates : List (Certificate args) := [sideFacts, headFacts]

private def headCell : Address 3 := 0
private def sideCell : Address 3 := 1

private def input (side : Address 3 := sideCell) : Tuple (Val 3) args :=
  .cons headCell (.cons side (.cons (8 : Word) (.cons (11 : Word) .nil)))

private def initial : Heap 3 := fun address => if address = sideCell then 4 else 1
private def final : Heap 3 := ((initial.write headCell 11).write sideCell 8).write sideCell 11

private def chosen : Result args := ⟨⟨1, 2⟩, headFacts, target⟩
private theorem selected : rewrite source certificates input = some chosen := rfl

private def versions (result : Result args) : Nat × Nat :=
  (result.candidate.removeVersion, result.candidate.overwriteVersion)

-- Store order takes priority over certificate order. Both Stores 1 and 3
-- are removable at this input.
example : (rewrite source [sideFacts] input).map versions = some (3, 4) := rfl
/-- info: some (1, 2) -/
#guard_msgs in
#eval (rewrite source certificates input).map versions

example : source.Returns input initial 4 final :=
  (rewrite_returns_iff input selected initial 4 final).mp
    ((target.returns_iff_denote input initial 4 final).mpr (by cbv))

-- The observing read blocks Store 1, and Store 3 can still be selected.
example : (rewrite (source headPort) certificates input).map versions = some (3, 4) := rfl
example : rewrite (source headPort) [headFacts] input = none := rfl

-- The same distinct ports can alias at this invocation.
example : rewrite source [headFacts] (input headCell) = none := rfl

private def noOverwrite : Graph args :=
  .store (.latest 0) (.arg headPort) (.arg early)
    (.store (.latest 1) (.arg sidePort) (.arg late) (.ret (.latest 2) (.arg late)))

example : rewrite noOverwrite certificates input = none := rfl

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection
