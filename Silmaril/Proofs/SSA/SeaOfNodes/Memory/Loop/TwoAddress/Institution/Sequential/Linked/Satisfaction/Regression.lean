module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction

open CategoryTheory
open RVSDG (Port Tuple)
open RVSDG.NestedTheta.Institution
open Linked.Fixture (combined first wiring inputs rightStore)
open Sequential.Fixture (captures graph initial)
open Memory.Diamond.Institution (reduct pullInput pullInput_get)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

private def lhs : Program combined := ⟨captures, first, graph, wiring⟩

-- Identify the right store value with the first stage's store capture.
-- The dependent right stop word continues to come from the first return.
private def identifyStore : combined ⟶ combined :=
  ⟨fun
    | .tail (.tail (.tail (.tail (.tail (.tail .head))))) => .tail (.tail (.tail .head))
    | port => port⟩

private def rhs : Program combined := lhs.map identifyStore
private abbrev entry : EntryModel combined := ⟨6, inputs⟩

example : rhs.numberedObserve entry initial = lhs.numberedObserve (reduct identifyStore entry) initial :=
  lhs.numbered_observe_map identifyStore entry initial

private def middle : Heap 6 := (initial.write 0 11).write 2 11
private def heapAfter (rightWord : Word) : Heap 6 :=
  (middle.write 3 rightWord).write 5 rightWord

private theorem lhsReturned : lhs.nativeReturns entry initial (3, 3, heapAfter 22) :=
  ⟨middle, ⟨1, rfl⟩, ⟨1, rfl⟩⟩

private theorem rhsReturned : rhs.nativeReturns entry initial (3, 3, heapAfter 11) :=
  ⟨middle, ⟨1, rfl⟩, ⟨1, rfl⟩⟩

private theorem mismatch :
    ¬ Agrees (lhs.nativeReturns entry) (rhs.nativeReturns entry) := by
  intro agrees
  have equations := (numbered_agrees lhs rhs entry).mpr agrees initial
  have left := (lhs.numbered_eq_some_iff entry initial (3, 3, heapAfter 22)).mpr lhsReturned
  have right := (rhs.numbered_eq_some_iff entry initial (3, 3, heapAfter 11)).mpr rhsReturned
  have equal := Part.some_inj.mp (left.symm.trans (equations.trans right))
  have cell := congrArg (fun raw => ((resultCodec 6).symm raw).2.2 3) equal
  change (22 : Word) = 11 at cell
  exact (by decide : (22 : Word) ≠ 11) cell

-- The actual existing room rejects this linked equation at count six.
private theorem unrestrictedFalse :
    ¬ (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 6)) (lhs.equation rhs) :=
  fun holds => mismatch ((equation_satisfaction lhs rhs 6).mp holds entry.input)

example : ¬ Agrees (lhs.colouredReturns entry) (rhs.colouredReturns entry) :=
  fun holds => mismatch ((coloured_agrees lhs rhs entry).mp holds)

private def run (p : Program combined) : Option (Word × Word × List Word) :=
  (p.runMemRef entry 8 ⟨initial⟩).map fun (word, nextWord, heap) =>
    (word, nextWord, (List.finRange 6).map heap.cell)

#guard run lhs == some (3, 3, [11, 73, 11, 22, 91, 22])
#guard run rhs == some (3, 3, [11, 73, 11, 11, 91, 11])

private abbrev extended : EntrySignature := ⟨.word :: combined.args⟩
private def insert : combined ⟶ extended := ⟨fun p => .tail p⟩
private def back : extended ⟶ combined := ⟨fun | .head => rightStore | .tail p => p⟩
private theorem insertion_split : insert ≫ back = 𝟙 combined := rfl
private abbrev extendedEntry : EntryModel extended := ⟨6, .cons (99 : Word) inputs⟩

-- The store-port identification and insertion are separate typed maps.
private def staged : Program extended := (lhs.map identifyStore).map insert
private def composed : Program extended := lhs.map (identifyStore ≫ insert)

example :
    staged.numberedObserve extendedEntry initial = lhs.numberedObserve (reduct identifyStore entry) initial :=
  lhs.numbered_observe_comp identifyStore insert extendedEntry initial

example : composed.colouredReturns extendedEntry initial (3, 3, heapAfter 11) := by
  unfold composed
  rw [lhs.map_comp identifyStore insert]
  apply (lhs.coloured_returns_comp identifyStore insert extendedEntry initial _).mpr
  exact (lhs.coloured_returns_iff (reduct identifyStore entry) initial _).mpr
    ((lhs.native_returns_map identifyStore entry initial _).mp rhsReturned)

private def runMemRef (p : Program extended) : Option (Word × Word × List Word) :=
  (p.runMemRef extendedEntry 8 ⟨initial⟩).map fun (word, nextWord, heap) =>
    (word, nextWord, (List.finRange 6).map heap.cell)

private def runNumbered (p : Program extended) : Option (Word × Word × List Word) :=
  (p.emitNumbered.graph.run (thetaRuntime 6) 2 (encodeInput initial extendedEntry.input)).map fun raw =>
    let (word, nextWord, heap) := (resultCodec 6).symm raw
    (word, nextWord, (List.finRange 6).map heap)

#guard runMemRef staged == some (3, 3, [11, 73, 11, 11, 91, 11])
#guard runMemRef composed == some (3, 3, [11, 73, 11, 11, 91, 11])
#guard runNumbered staged == some (3, 3, [11, 73, 11, 11, 91, 11])
#guard runNumbered composed == some (3, 3, [11, 73, 11, 11, 91, 11])

private def leftStore : Port combined.args .word := .tail (.tail (.tail .head))

private theorem outside_image : ¬ InReductImage identifyStore inputs := by
  rintro ⟨targetInput, pulled⟩
  change (⟨6, pullInput (EntrySignature.Hom.port identifyStore) targetInput⟩ : EntryModel combined) =
    ⟨6, inputs⟩ at pulled
  have values : pullInput (EntrySignature.Hom.port identifyStore) targetInput = inputs := by
    simpa only [EntryModel.mk.injEq, heq_eq_eq, true_and] using pulled
  have left := congrArg (fun input : Tuple (Val 6) combined.args => input.get leftStore) values
  have right := congrArg (fun input : Tuple (Val 6) combined.args => input.get rightStore) values
  rw [pullInput_get] at left right
  change targetInput.get leftStore = (11 : Word) at left
  change targetInput.get leftStore = (22 : Word) at right
  exact (by decide : (11 : Word) ≠ 22) (left.symm.trans right)

example : ¬ InReductImage (identifyStore ≫ insert) inputs := fun image =>
  outside_image ((in_image_comp_iff_of_surjective identifyStore insert
    (in_image_of_retraction insert back insertion_split) inputs).mp image)

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

-- After identification, global target truth can hold while the original
-- source sentence fails. Both re-emission paths give the same equation.
example : (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 6))
    (composed.equation (rhs.map (identifyStore ≫ insert))) := by
  have equal : rhs.map identifyStore = lhs.map identifyStore :=
    (lhs.map_comp identifyStore identifyStore).symm.trans (congrArg (fun h => lhs.map h) identify_idempotent)
  unfold composed
  rw [lhs.map_comp identifyStore insert, rhs.map_comp identifyStore insert, equal]
  exact (equation_satisfaction _ _ 6).mpr fun _ _ _ => Iff.rfl

-- A spare typed slot alone admits a retraction and reflects unrestricted truth.
example : ¬ (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 6))
    ((lhs.map insert).equation (rhs.map insert)) := fun holds =>
  unrestrictedFalse ((equation_satisfaction_iff_of_surjective insert lhs rhs 6
    (in_image_of_retraction insert back insertion_split)).mp holds)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction
