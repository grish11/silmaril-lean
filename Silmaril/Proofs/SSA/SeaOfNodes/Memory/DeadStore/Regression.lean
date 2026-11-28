module

import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore

open RVSDG (Origin Port Tuple)
open Memory.Forwarding.Disjoint (Certificate)

private abbrev args : List ValueSort := [.address, .address, .address, .word]

private def observed : Port args .address := .head
private def reader : Port args .address := .tail .head
private def logger : Port args .address := .tail (.tail .head)
private def early : Port args .word := .tail (.tail (.tail .head))

private def before : Origin args [[.word], [.word]] .word := .output (1 : Fin 2) .head
private def loaded : Origin args [[.word], [.word]] .word := .output (0 : Fin 2) .head

-- Read head before the removable Store. The intervening read supplies
-- both the logging Store and Return. The last Store restores the old head.
private def source (readPort : Port args .address := reader) : Graph args :=
  .load (.latest 0) (.arg observed)
    (.store (.latest 0) (.arg observed) (.arg early)
      (.load (.latest 1) (.arg readPort)
        (.store (.latest 1) (.arg logger) loaded
          (.store (.latest 2) (.arg observed) before (.ret (.latest 3) loaded)))))

private def target : Graph args :=
  .load (.latest 0) (.arg observed)
    (.load (.latest 0) (.arg reader)
      (.store (.latest 0) (.arg logger) loaded
        (.store (.latest 1) (.arg observed) before (.ret (.latest 2) loaded))))

private def candidate : Candidate := ⟨1, 3⟩
private def facts : Certificate args := ⟨observed, [reader]⟩

private def headCell : Address 4 := 0
private def readCell : Address 4 := 1
private def logCell : Address 4 := 2

private def input (readAt : Address 4 := readCell) (logAt : Address 4 := logCell) :
    Tuple (Val 4) args :=
  .cons headCell (.cons readAt (.cons logAt (.cons (8 : Word) .nil)))

private def initial : Heap 4 := fun address =>
  if address = headCell then 1 else if address = readCell then 2 else 99

private def final : Heap 4 := (initial.write logCell 2).write headCell 1
private theorem checked : rewrite source candidate facts input = some target := rfl

example : rewriteWith source candidate facts = some target := rfl
example : target.denote input initial = (2, final) := by cbv
example : source.Returns input initial 2 final :=
  (rewrite_returns_iff input checked initial 2 final).mp
    ((target.returns_iff_denote input initial 2 final).mpr (by cbv))

-- The intervening Store may write the observed cell. Its value depends
-- only on the certified distinct read, and the later overwrite still runs.
private def aliasedLogger : Tuple (Val 4) args := input readCell headCell
example : rewrite source candidate facts aliasedLogger = some target := rfl
example : target.denote aliasedLogger initial = (2, (initial.write headCell 2).write headCell 1) := by cbv

-- A different reader port can still name the same concrete cell.
private def aliasedReader : Tuple (Val 4) args := input headCell
example : rewrite source candidate facts aliasedReader = none := rfl
example : source.denote aliasedReader initial =
    (8, ((initial.write headCell 8).write logCell 8).write headCell 1) := by cbv
example : target.denote aliasedReader initial = (1, (initial.write logCell 1).write headCell 1) := by cbv

example : rewriteWith source candidate ⟨observed, []⟩ = none := rfl
example : rewriteWith (source observed) candidate ⟨observed, [observed]⟩ = none := rfl
example : rewriteWith source ⟨1, 2⟩ facts = none := rfl

example : Search.discover source 1 facts = some candidate := rfl

private theorem discovered : Search.rewrite source 1 facts input = some target := rfl

example : source.Returns input initial 2 final :=
  (Search.rewrite_returns_iff input discovered initial 2 final).mp
    ((target.returns_iff_denote input initial 2 final).mpr (by cbv))

-- The first overwrite ends the search. An observing read after that
-- overwrite is safe and can still feed Return.
private def twoOverwrites : Graph args :=
  .store (.latest 0) (.arg observed) (.arg early)
    (.store (.latest 1) (.arg observed) (.arg early)
      (.load (.latest 2) (.arg observed)
        (.store (.latest 2) (.arg observed) (.arg early) (.ret (.latest 3) (.output (0 : Fin 1) .head)))))

example : Search.discover twoOverwrites 1 ⟨observed, []⟩ = some ⟨1, 2⟩ := rfl

example : Search.discover (source observed) 1 ⟨observed, [observed]⟩ = none := rfl
example : Search.discover source 1 ⟨observed, []⟩ = none := rfl
example : Search.rewrite source 1 facts aliasedReader = none := rfl

private def noMatchingOverwrite : Graph args :=
  .store (.latest 0) (.arg observed) (.arg early)
    (.store (.latest 1) (.arg logger) (.arg early) (.ret (.latest 2) (.arg early)))

example : Search.discover noMatchingOverwrite 1 ⟨observed, []⟩ = none := rfl

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore
