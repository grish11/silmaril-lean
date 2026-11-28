module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom

open CategoryTheory Silmaril.Logic.Institution
open Fixture
open RVSDG.NestedTheta.Institution
open RuntimeRoom (GeneratedProgram)
open Memory.Diamond.Institution renaming Model → EntryModel

private def equation : Institution.Sentence captures := .equation graph coincidentGraph

private def model : EntryModel captures := ⟨4, input 1⟩

private def numbered : RuntimeRoom.Sentence captures := (RuntimeRoom.comparison.ρ.app captures).sen equation

private def coloured : RuntimeRoom.Sentence captures := (comparison.ρ.app captures).sen numbered

private theorem completes (g : Graph args) (heap : Heap 4)
    (returned : nativeReturns (P := captures) g model initial 0 heap) :
    (GeneratedProgram.lower g).Completes model initial (encodeResult 0 heap) :=
  let program := GeneratedProgram.lower g
  (program.completes_iff_numbered model initial _).mpr
    ((program.observe_eq_some_iff_native model initial 0 heap).mpr returned)

-- Actual completed markings have equal returned words and differ at cell 1.
example : ¬ (room captures).Sat (Discrete.mk model) coloured := by
  intro holds
  let lhs := GeneratedProgram.lower graph
  let rhs := GeneratedProgram.lower coincidentGraph
  have swapped := (lhs.petriObserve_eq_some_iff model initial (encodeResult 0 final)).mpr
    (completes graph final ⟨2, rfl⟩)
  have aliasedReturn := (rhs.petriObserve_eq_some_iff model initial (encodeResult 0 aliased)).mpr
    (completes coincidentGraph aliased ⟨1, rfl⟩)
  have agrees : lhs.petriObserve model initial = rhs.petriObserve model initial := holds initial
  have equal := Part.some_inj.mp (aliasedReturn.symm.trans (agrees.symm.trans swapped))
  have cell := congrArg (fun value => value.get (.tail .head) (1 : Address 4)) equal
  change (5 : Word) = 0 at cell
  exact (by decide : (5 : Word) ≠ 0) cell

private def reemitted : RuntimeRoom.Sentence captures := (corridor identifyAddresses).sen coloured

example : ((corridor identifyAddresses).mod.obj (Discrete.mk model)).as.input = input 0 := rfl

private theorem after_identification (targetModel : EntryModel captures) :
    (room captures).Sat (Discrete.mk targetModel) reemitted := by
  have natural := congrArg (fun f : RuntimeRoom.room captures ⟶ room captures => f.sen numbered)
    (comparison_natural identifyAddresses)
  change (comparison.ρ.app captures).sen ((RuntimeRoom.corridor identifyAddresses).sen numbered) =
    reemitted at natural
  rw [← natural]
  apply ((comparison.ρ.app captures).sat (Discrete.mk targetModel) (numbered.map identifyAddresses)).mpr
  apply (RuntimeRoom.Sentence.lower_satisfaction (equation.map identifyAddresses) targetModel).mpr
  intro heap word final
  exact Iff.rfl

example : (room captures).Sat (Discrete.mk model) reemitted :=
  after_identification model

-- Every target valuation contributes just its pullback to the source.
example : (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 4)) reemitted.numbered :=
  (numbered_satisfaction_map identifyAddresses coloured 4).mpr fun input =>
    (holds_map identifyAddresses coloured ⟨4, input⟩).mp (after_identification ⟨4, input⟩)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom
