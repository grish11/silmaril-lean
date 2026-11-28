module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.MemRef.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom

open CategoryTheory Silmaril.Logic.Institution
open Fixture
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Model → EntryModel

private def equation : Institution.Sentence captures := .equation graph coincidentGraph

private def model : EntryModel captures := ⟨4, input 1⟩

private def emitted : Sentence captures := (comparison.ρ.app captures).sen equation

-- Full observations distinguish the two emitted roots at distinct addresses.
example : ¬ (room captures).Sat (Discrete.mk model) emitted := by
  intro holds
  let lhs := GeneratedProgram.lower graph
  let rhs := GeneratedProgram.lower coincidentGraph
  have swapped : lhs.observe model initial = Part.some (encodeResult 0 final) :=
    (lhs.observe_eq_some_iff_native model initial 0 final).mpr ⟨2, rfl⟩
  have aliasedReturn : rhs.observe model initial = Part.some (encodeResult 0 aliased) :=
    (rhs.observe_eq_some_iff_native model initial 0 aliased).mpr ⟨1, rfl⟩
  have agrees : lhs.observe model initial = rhs.observe model initial := holds initial
  have equal := Part.some_inj.mp (aliasedReturn.symm.trans (agrees.symm.trans swapped))
  have cell := congrArg (fun value => value.get (.tail .head) (1 : Address 4)) equal
  change (5 : Word) = 0 at cell
  exact (by decide : (5 : Word) ≠ 0) cell

private def reemitted : Sentence captures := (corridor identifyAddresses).sen emitted

private theorem native_after_identification : (equation.map identifyAddresses).HoldsAt 4 :=
  fun _ _ _ _ => Iff.rfl

example : ((corridor identifyAddresses).mod.obj (Discrete.mk model)).as.input = input 0 := rfl

private theorem reemitted_holds : (room captures).Sat (Discrete.mk model) reemitted := by
  have natural := congrArg (fun f : Institution.room captures ⟶ room captures => f.sen equation)
    (comparison_natural identifyAddresses)
  change (comparison.ρ.app captures).sen (equation.map identifyAddresses) = reemitted at natural
  rw [← natural]
  exact ((comparison.ρ.app captures).sat (Discrete.mk model) (equation.map identifyAddresses)).mpr
    (native_after_identification model.input)

-- The existing numbered room sees only the identified valuations through this translation.
example : (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 4)) reemitted.numbered :=
  (emitted.numbered_satisfaction_map identifyAddresses 4).mpr fun input =>
    (emitted.satisfaction (reduct identifyAddresses ⟨4, input⟩)).mpr
      ((equation.satisfaction_map identifyAddresses ⟨4, input⟩).mp (native_after_identification input))

private def reemittedMemRef : MemRefRoom.Sentence captures :=
  (MemRefRoom.corridor identifyAddresses).sen ((MemRefRoom.comparison.ρ.app captures).sen equation)

-- The direct MemRef comparison and the numbered path agree after re-emission.
example : (MemRefRoom.room captures).Sat (Discrete.mk model) reemittedMemRef := by
  have factor := congrArg (fun f : Institution.room captures ⟶ MemRefRoom.room captures => f.sen equation)
    (comparisonCorridor_factors captures)
  have equal : reemitted.toMemRef = reemittedMemRef :=
    (emitted.toMemRef_map identifyAddresses).trans (congrArg (MemRefRoom.Sentence.map identifyAddresses) factor)
  rw [← equal]
  exact (reemitted.toMemRef_satisfaction model).mpr reemitted_holds

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom
