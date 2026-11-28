module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Port Tuple)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (reduct pullInput pullInput_get)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Linked.Satisfaction (InReductImage)
open Sequential.Fixture (captures graph initial right)
open Linked.Fixture (combined first wiring inputs rightStore)
open Triple.Fixture (thirdWiring entryModel afterFirst afterSecond expected)

private def original : Program combined := ⟨⟨captures, first, graph, wiring⟩, captures, graph, thirdWiring⟩

private def leftStore : Port combined.args .word := .tail (.tail (.tail .head))

-- Feed both store captures from the left word slot. Then insert a spare word slot.
private def identifyStore : combined ⟶ combined :=
  ⟨fun
    | .tail (.tail (.tail (.tail (.tail (.tail .head))))) => leftStore
    | port => port⟩

private abbrev extended : EntrySignature := ⟨.word :: combined.args⟩
private def insert : combined ⟶ extended := ⟨fun p => .tail p⟩
private abbrev extendedEntry : EntryModel extended := ⟨6, .cons (99 : Word) inputs⟩

private def identified := original.map identifyStore
private def equation : Sentence combined := .equation original identified

private theorem identify_idempotent : identifyStore ≫ identifyStore = identifyStore := by
  apply congrArg EntrySignature.Hom.mk
  funext sort port
  cases port with | head => rfl | tail p => ?_
  cases p with | head => rfl | tail p => ?_
  cases p with | head => rfl | tail p => ?_
  cases p with | head => rfl | tail p => ?_
  cases p with | head => rfl | tail p => ?_
  cases p with | head => rfl | tail p => ?_
  cases p with | head => rfl | tail p => cases p

private theorem mergedPrograms : original.map (identifyStore ≫ insert) = identified.map (identifyStore ≫ insert) := by
  unfold identified
  rw [← original.map_comp identifyStore (identifyStore ≫ insert), ← Category.assoc, identify_idempotent]

example : corridor .memref (identifyStore ≫ insert) = corridor .memref identifyStore ≫ corridor .memref insert :=
  corridor_comp .memref identifyStore insert

private theorem targetTrue : (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 6))
    ((equation.map (identifyStore ≫ insert)).numbered) := by
  apply ((equation.map (identifyStore ≫ insert)).room_satisfaction 6).mpr
  intro input
  change (Sentence.equation (original.map (identifyStore ≫ insert))
    (identified.map (identifyStore ≫ insert))).NumberedHolds ⟨6, input⟩
  rw [← mergedPrograms]
  exact fun _ _ => Iff.rfl

-- The institutional component transfers the re-emitted sentence at the actual target model.
example : (room .coloured extended).Sat (Discrete.mk extendedEntry)
    ((equation.map identifyStore).map insert) := by
  rw [← equation.map_comp identifyStore insert]
  exact ((comparison .numbered .coloured).satisfaction extended (Discrete.mk extendedEntry)
    (equation.map (identifyStore ≫ insert))).mpr
      (((equation.map (identifyStore ≫ insert)).room_satisfaction 6).mp targetTrue extendedEntry.input)

private theorem outside_image : ¬ InReductImage (identifyStore ≫ insert) inputs := by
  rintro ⟨targetInput, equal⟩
  change (⟨6, pullInput (EntrySignature.Hom.port (identifyStore ≫ insert)) targetInput⟩ : EntryModel combined) =
    ⟨6, inputs⟩ at equal
  have values : pullInput (EntrySignature.Hom.port (identifyStore ≫ insert)) targetInput = inputs := by
    simpa only [EntryModel.mk.injEq, heq_eq_eq, true_and] using equal
  have left := congrArg (fun input : Tuple (Val 6) combined.args => input.get leftStore) values
  have right := congrArg (fun input : Tuple (Val 6) combined.args => input.get rightStore) values
  rw [pullInput_get] at left right
  change targetInput.get (.tail leftStore) = (11 : Word) at left
  change targetInput.get (.tail leftStore) = (22 : Word) at right
  exact (by decide : (11 : Word) ≠ 22) (left.symm.trans right)

private def changedMiddle : Heap 6 := (afterFirst.write 3 11).write 5 11
private def changed : Triple.Result 6 := (3, 3, 11, changedMiddle.write (right 0) 3)

private theorem originalReturns : original.numberedReturns entryModel initial expected :=
  (Triple.returns_iff_stages first graph graph wiring thirdWiring entryModel initial _ 3 3 22).mpr
    ⟨afterFirst, afterSecond, ⟨2, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩⟩

private theorem identifiedReturns : identified.numberedReturns entryModel initial changed :=
  (original.numbered_returns_map identifyStore entryModel initial changed).mpr
    ((Triple.returns_iff_stages first graph graph wiring thirdWiring (reduct identifyStore entryModel)
      initial _ 3 3 11).mpr ⟨afterFirst, changedMiddle, ⟨2, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩⟩)

private theorem sourceFalse : ¬ equation.NumberedHolds entryModel := by
  intro holds
  have expectedObserved := (identified.numbered_eq_some_iff entryModel initial expected).mpr
    ((holds initial expected).mp originalReturns)
  have changedObserved := (identified.numbered_eq_some_iff entryModel initial changed).mpr identifiedReturns
  have equal := (resultCodec 6).injective (Part.some_inj.mp (expectedObserved.symm.trans changedObserved))
  have word := congrArg (fun result : Triple.Result 6 => result.2.2.1) equal
  exact (by decide : (22 : Word) ≠ 11) word

-- The exact restriction admits the re-emitted truth. The unrestricted source room rejects it.
example : (∀ input : Tuple (Val 6) combined.args, InReductImage (identifyStore ≫ insert) input →
      (room .memref combined).Sat (Discrete.mk ⟨6, input⟩) equation) ∧
    ¬ (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 6)) equation.numbered :=
  ⟨(equation.room_satisfaction_image .memref (identifyStore ≫ insert) 6).mp targetTrue,
    fun holds => sourceFalse ((equation.room_satisfaction 6).mp holds inputs)⟩

example : ¬ InReductImage (identifyStore ≫ insert) entryModel.input := outside_image

example : ¬ (corridor .memref (identifyStore ≫ insert)).ModelExpansive :=
  fun expands => outside_image
    ((corridor_modelExpansive_iff .memref (identifyStore ≫ insert)).mp expands 6 inputs)

private def discardSpare : extended ⟶ combined :=
  ⟨fun | .head => rightStore | .tail port => port⟩

example : (corridor .memref insert).ModelExpansive :=
  corridor_modelExpansive_of_retraction .memref insert discardSpare rfl

private def staged : Program extended := identified.map insert
private def composed : Program extended := original.map (identifyStore ≫ insert)

example : staged.colouredReturns extendedEntry initial changed :=
  (staged.coloured_returns_iff extendedEntry initial changed).mpr
    ((identified.numbered_returns_map insert extendedEntry initial changed).mpr identifiedReturns)

private def run {P : EntrySignature} (p : Program P) (model : EntryModel P)
    (heap : Heap model.cells) : Option (Word × Word × Word × List Word) :=
  (p.runMemRef model 11 ⟨heap⟩).map fun (first, second, third, buffer) =>
    (first, second, third, (List.finRange model.cells).map buffer.cell)

#guard run original entryModel initial == some (3, 3, 22, [11, 73, 11, 3, 91, 22])
#guard run staged extendedEntry initial == some (3, 3, 11, [11, 73, 11, 3, 91, 11])
#guard run composed extendedEntry initial == some (3, 3, 11, [11, 73, 11, 3, 91, 11])

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction
