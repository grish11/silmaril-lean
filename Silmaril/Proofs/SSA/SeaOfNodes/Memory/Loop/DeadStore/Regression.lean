module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Search.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore

open RVSDG (Origin Port Tuple)
open Memory.DeadStore (Candidate)
open Memory.Forwarding.Disjoint (Certificate)

private abbrev args : List ValueSort := [.address, .address, .address, .word]

private def headPort : Port args .address := .head
private def tailPort : Port args .address := .tail .head
private def logPort : Port args .address := .tail (.tail .head)
private def stopPort : Port args .word := .tail (.tail (.tail .head))

private def oldHead : Origin args [[.word], [.word]] .word := .output (1 : Fin 2) .head
private def oldTail : Origin args [[.word], [.word]] .word := .output (0 : Fin 2) .head

-- Load the old head before the dead write. The intervening read feeds
-- the unconditional overwrite before the old-head tail test.
private def source (reader : Port args .address := tailPort) : Graph args :=
  ⟨.load (.latest 0) (.arg headPort)
    (.store (.latest 0) (.arg headPort) (.arg stopPort)
      (.load (.latest 1) (.arg reader)
        (.store (.latest 1) (.arg tailPort) (.arg stopPort)
          (.store (.latest 2) (.arg headPort) oldTail
            (.store (.latest 3) (.arg logPort) oldHead (.ret (.latest 4) oldHead)))))),
    rfl, stopPort⟩

private def target : Graph args :=
  ⟨.load (.latest 0) (.arg headPort)
    (.load (.latest 0) (.arg tailPort)
      (.store (.latest 0) (.arg tailPort) (.arg stopPort)
        (.store (.latest 1) (.arg headPort) oldTail
          (.store (.latest 2) (.arg logPort) oldHead (.ret (.latest 3) oldHead))))),
    rfl, stopPort⟩

private def candidate : Candidate := ⟨1, 3⟩
private def facts : Certificate args := ⟨headPort, [tailPort]⟩

private def headCell : Address 4 := 0
private def tailCell : Address 4 := 1
private def logCell : Address 4 := 2

private def input (tail : Address 4 := tailCell) : Tuple (Val 4) args :=
  .cons headCell (.cons tail (.cons logCell (.cons (0 : Word) .nil)))

private theorem checked : rewrite source candidate facts input = some target := rfl
private theorem static : rewriteWith source candidate facts = some target :=
  ((rewrite_eq_some_iff input).mp checked).1
private theorem valid : facts.Valid input :=
  ((rewrite_eq_some_iff input).mp checked).2

private def initial (head : Word) : Heap 4 := fun address =>
  if address = headCell then head else if address = tailCell then 2 else 99

private def after (heap : Heap 4) (head tail : Word) : Heap 4 :=
  ((heap.write tailCell 0).write headCell tail).write logCell head

private def firstHeap : Heap 4 := after (initial 1) 1 2
private def secondHeap : Heap 4 := after firstHeap 2 0
private def exitHeap : Heap 4 := after secondHeap 0 0

example : source.step input (initial 1) = .inr firstHeap :=
  (rewriteWith_step static input valid (initial 1)).symm.trans (by cbv)
example : target.step input firstHeap = .inr secondHeap := by cbv
example : target.evalAfter input (initial 1) 2 = some (0, exitHeap) := by cbv

example : source.Returns input (initial 1) 0 exitHeap :=
  (rewriteWith_returns_iff static input valid (initial 1) 0 exitHeap).mp
    ⟨2, (target.returnsAfter_iff_evalAfter input (initial 1) 2 0 exitHeap).mpr (by cbv)⟩

-- A zero-backedge exit still executes the overwrite and the logging Store.
example : target.evalAfter input (initial 0) 0 = some (0, after (initial 0) 0 2) := by cbv

example : rewriteWith (source headPort) candidate ⟨headPort, [headPort]⟩ = none := rfl
example : rewriteWith source ⟨1, 2⟩ facts = none := rfl
example : rewriteWith source ⟨1, 5⟩ facts = none := rfl

-- Aliasing the intervening reader would change the next head value.
example : rewrite source candidate facts (input headCell) = none := rfl
example : (source.body.denote (input headCell) (initial 1)).2.read headCell = 0 := by cbv
example : (target.body.denote (input headCell) (initial 1)).2.read headCell = 1 := by cbv

private theorem discovered : Search.rewrite source 1 facts input = some target := rfl

example : source.ReturnsAfter input (initial 1) 2 0 exitHeap :=
  (Search.rewrite_returnsAfter_iff input discovered (initial 1) 2 0 exitHeap).mp
    ((target.returnsAfter_iff_evalAfter input (initial 1) 2 0 exitHeap).mpr (by cbv))

example : Search.rewrite (source headPort) 1 facts input = none := rfl
example : Search.rewrite source 1 facts (input headCell) = none := rfl

private def singleStore : Graph args :=
  ⟨.load (.latest 0) (.arg headPort)
    (.store (.latest 0) (.arg headPort) (.arg stopPort)
      (.ret (.latest 1) (.output (0 : Fin 1) .head))), rfl, stopPort⟩

-- Reentering this body still provides no overwrite in this activation.
example : Search.rewrite singleStore 1 ⟨headPort, []⟩ input = none := rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore
