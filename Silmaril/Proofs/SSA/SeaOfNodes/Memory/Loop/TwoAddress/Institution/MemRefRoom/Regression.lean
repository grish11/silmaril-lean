module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom

open CategoryTheory Silmaril.Logic.Institution
open Fixture
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Model → EntryModel

private def equation : Institution.Sentence captures := .equation graph coincidentGraph
private def model : EntryModel captures := ⟨4, input 1⟩

private def emitted : Sentence captures := (comparison.ρ.app captures).sen equation

-- The two emitted programs return the same word and different full heaps
-- at this distinct-address valuation.
example : ¬ (room captures).Sat (Discrete.mk model) emitted := by
  intro holds
  let lhs := GeneratedProgram.lower graph
  let rhs := GeneratedProgram.lower coincidentGraph
  have swapped : lhs.Returns model ⟨initial⟩ (0, ⟨final⟩) :=
    (lhs.returns_iff_native model ⟨initial⟩ 0 ⟨final⟩).mpr ⟨2, rfl⟩
  have aliasedReturn : rhs.Returns model ⟨initial⟩ (0, ⟨aliased⟩) :=
    (rhs.returns_iff_native model ⟨initial⟩ 0 ⟨aliased⟩).mpr ⟨1, rfl⟩
  have agrees : lhs.Returns model ⟨initial⟩ (0, ⟨final⟩) ↔
      rhs.Returns model ⟨initial⟩ (0, ⟨final⟩) := holds ⟨initial⟩ 0 ⟨final⟩
  have numberedEqual := ((rhs.returns_iff_numbered model ⟨initial⟩ 0 ⟨aliased⟩).mp aliasedReturn).symm.trans
    ((rhs.returns_iff_numbered model ⟨initial⟩ 0 ⟨final⟩).mp (agrees.mp swapped))
  have cell := congrArg (fun value => value.get (.tail .head) (1 : Address 4))
    (Part.some_inj.mp numberedEqual)
  change (5 : Word) = 0 at cell
  exact (by decide : (5 : Word) ≠ 0) cell

private def reemitted : Sentence captures := (corridor identifyAddresses).sen emitted

private theorem native_after_identification : (equation.map identifyAddresses).HoldsAt 4 :=
  fun _ _ _ _ => Iff.rfl

-- The capture map is genuinely nonidentity at the selected target valuation.
example : (reduct identifyAddresses model).input = input 0 := rfl

example : (room captures).Sat (Discrete.mk model) reemitted := by
  have natural := congrArg (fun f : Institution.room captures ⟶ room captures => f.sen equation)
    (comparison_natural identifyAddresses)
  change (comparison.ρ.app captures).sen (equation.map identifyAddresses) = reemitted at natural
  rw [← natural]
  exact ((comparison.ρ.app captures).sat (Discrete.mk model) (equation.map identifyAddresses)).mpr
    (native_after_identification model.input)

-- The same re-emission has the corresponding sentence in the existing
-- numbered room at its canonical model. This check ranges over target inputs.
example : (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 4)) reemitted.numbered :=
  (emitted.numbered_satisfaction_map identifyAddresses 4).mpr fun input =>
    (emitted.satisfaction (reduct identifyAddresses ⟨4, input⟩)).mpr ((equation.satisfaction_map identifyAddresses ⟨4, input⟩).mp
      (native_after_identification input))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom
