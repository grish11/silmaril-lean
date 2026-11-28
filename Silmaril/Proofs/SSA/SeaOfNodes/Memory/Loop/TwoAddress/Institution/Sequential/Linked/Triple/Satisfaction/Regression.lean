module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction

open CategoryTheory
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Sequential.Fixture (captures graph initial left right)
open Linked.Fixture (combined first wiring inputs)
open Triple.Fixture (thirdWiring entryModel afterFirst afterSecond expected thirdInput)

private def original : Program combined := ⟨⟨captures, first, graph, wiring⟩, captures, graph, thirdWiring⟩

private theorem originalReturns : original.numberedReturns entryModel initial expected :=
  (Triple.returns_iff_stages first graph graph wiring thirdWiring entryModel initial _ 3 3 22).mpr
    ⟨afterFirst, afterSecond, ⟨2, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩⟩

private abbrev extended : EntrySignature := ⟨.word :: combined.args⟩
private def insert : combined ⟶ extended := ⟨fun port => .tail port⟩

-- Use the added word slot instead of the old right store port.
private def aliasStore : combined ⟶ extended :=
  ⟨fun
    | .tail (.tail (.tail (.tail (.tail (.tail .head))))) => .head
    | port => .tail port⟩

private abbrev extendedEntry : EntryModel extended := ⟨6, .cons (22 : Word) inputs⟩
private def lhs := original.map insert
private def rhs := original.map aliasStore
private def forwarded : Sentence extended := .equation lhs rhs

private theorem forwardedHolds : forwarded.NumberedHolds extendedEntry := by
  intro heap out
  exact (original.numbered_returns_map insert extendedEntry heap out).trans
    (original.numbered_returns_map aliasStore extendedEntry heap out).symm

example : forwarded.MemRefHolds extendedEntry :=
  (forwarded.memref_satisfaction extendedEntry).mpr forwardedHolds

example : forwarded.ColouredHolds extendedEntry :=
  (forwarded.coloured_satisfaction extendedEntry).mpr forwardedHolds

-- The accepted equation compares actual re-emissions. At this heap the
-- third word reads the forwarded 22, and the return retains every cell.
example : lhs.memrefReturns extendedEntry initial expected :=
  (lhs.memref_returns_iff extendedEntry initial expected).mpr
    ((original.numbered_returns_map insert extendedEntry initial expected).mpr originalReturns)

example : rhs.colouredReturns extendedEntry initial expected :=
  (rhs.coloured_returns_iff extendedEntry initial expected).mpr
    ((original.numbered_returns_map aliasStore extendedEntry initial expected).mpr originalReturns)

private def runMemRef {P : EntrySignature} (p : Program P) (model : EntryModel P)
    (heap : Heap model.cells) : Option (Word × Word × Word × List Word) :=
  (p.runMemRef model 11 ⟨heap⟩).map fun (first, second, third, buffer) =>
    (first, second, third, (List.finRange model.cells).map buffer.cell)

#guard runMemRef lhs extendedEntry initial == some (3, 3, 22, [11, 73, 11, 3, 91, 22])
#guard runMemRef rhs extendedEntry initial == some (3, 3, 22, [11, 73, 11, 3, 91, 22])

private def thirdRestore : Graph captures.args :=
  { graph with
    activation := ⟨.load (.latest 0) (.arg .head)
      (.store (.latest 0) (.arg .head) (.output 0 .head) (.ret (.latest 1) (.output 0 .head))),
      rfl, graph.activation.stop⟩ }

private def restore : Program combined := { original with third := thirdRestore }
private def incompatible : Sentence combined := .equation original restore

private def restoredHeap : Heap 6 := afterSecond.write (right 0) 22

private theorem restoreReturns : restore.numberedReturns entryModel initial (3, 3, 22, restoredHeap) :=
  (Triple.returns_iff_stages first graph thirdRestore wiring thirdWiring entryModel initial _ 3 3 22).mpr
    ⟨afterFirst, afterSecond, ⟨2, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩⟩

-- The three words coincide. Storing the loaded value retains 22 at
-- cell 3, while the original stores 3 there.
private theorem incompatibleFalse : ¬ incompatible.NumberedHolds entryModel := by
  intro holds
  have observed := (restore.numbered_eq_some_iff entryModel initial expected).mpr
    ((holds initial expected).mp originalReturns)
  have restoreObserved := (restore.numbered_eq_some_iff entryModel initial (3, 3, 22, restoredHeap)).mpr restoreReturns
  have equal := (resultCodec 6).injective (Part.some_inj.mp (observed.symm.trans restoreObserved))
  have cell := congrArg (fun out : Triple.Result 6 => out.2.2.2 3) equal
  exact (by decide : (3 : Word) ≠ 22) cell

example : ¬ (incompatible.map insert).MemRefHolds extendedEntry :=
  fun holds => incompatibleFalse ((incompatible.memref_satisfaction_map insert extendedEntry).mp holds)

example : ¬ (incompatible.map insert).ColouredHolds extendedEntry :=
  fun holds => incompatibleFalse ((incompatible.coloured_satisfaction_map insert extendedEntry).mp holds)

example : ¬ (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 6))
    (incompatible.map insert).numbered :=
  fun holds => incompatibleFalse ((incompatible.room_satisfaction_map insert 6).mp holds extendedEntry.input)

#guard runMemRef restore entryModel initial == some (3, 3, 22, [11, 73, 11, 22, 91, 22])

private def returnStop {args : List ValueSort} (loop : Graph args) : Graph args :=
  { loop with
    activation := ⟨.load (.latest 0) (.arg .head)
      (.store (.latest 0) (.arg .head) (.output 0 .head) (.ret (.latest 1) (.arg loop.activation.stop))),
      rfl, loop.activation.stop⟩ }

private def alwaysExits : Program combined :=
  ⟨⟨captures, returnStop first, returnStop graph, wiring⟩, captures, returnStop graph, thirdWiring⟩

private theorem totalNumbered : (Sentence.terminates alwaysExits).NumberedHolds entryModel := by
  intro heap
  let firstHeap := heap.write (left 0) (heap (left 0))
  let secondHeap := firstHeap.write (right 0) (firstHeap (right 0))
  let final := secondHeap.write (right 0) (secondHeap (right 0))
  refine ⟨(3, 3, 22, final), ?_⟩
  exact (Triple.returns_iff_stages (returnStop first) (returnStop graph) (returnStop graph)
    wiring thirdWiring entryModel heap final 3 3 22).mpr
      ⟨firstHeap, secondHeap, ⟨1, rfl⟩, ⟨1, rfl⟩, ⟨1, rfl⟩⟩

example : ((Sentence.terminates alwaysExits).map insert).MemRefHolds extendedEntry :=
  ((Sentence.terminates alwaysExits).memref_satisfaction_map insert extendedEntry).mpr totalNumbered

example : ((Sentence.terminates alwaysExits).map insert).ColouredHolds extendedEntry :=
  ((Sentence.terminates alwaysExits).coloured_satisfaction_map insert extendedEntry).mpr totalNumbered

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction
