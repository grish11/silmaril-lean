module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Splice
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature} {cells : Nat} {args : List ValueSort}

private theorem stage_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (initial final : Heap cells) (word : Word) :
    (∃ fuel, TwoAddress.MemRef.runFuel graph input fuel ⟨initial⟩ = some (word, ⟨final⟩)) ↔
      (Petri.lower graph).Returns (thetaRuntime cells) (encodeInput initial input) (encodeResult word final) :=
  (TwoAddress.MemRef.petri_finishes_iff_runFuel graph input initial word final).symm.trans
    (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _)

theorem returns_iff_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (f : Boundary.Wiring P.args Q.args) (g : Boundary.Wiring Q.args R.args) (model : EntryModel P)
    (initial final : Heap model.cells) (x y z : Word) :
    (∃ fuel, runFuel first second third f g model.input fuel ⟨initial⟩ = some (x, y, z, ⟨final⟩)) ↔
      (Triple.lower first second third f g).Returns (thetaRuntime model.cells)
        (encodeInput initial model.input) (Triple.resultCodec model.cells (x, y, z, final)) := by
  rw [returns_iff_pair_then_third, Triple.returns_iff_stages]
  constructor
  · rintro ⟨pairFuel, thirdFuel, ⟨secondHeap⟩, pairRun, thirdRun⟩
    obtain ⟨firstFuel, secondFuel, ⟨firstHeap⟩, firstRun, secondRun⟩ :=
      (Linked.MemRef.returns_iff_stages first second f model.input ⟨initial⟩ x y ⟨secondHeap⟩).mp
        ⟨pairFuel, pairRun⟩
    exact ⟨firstHeap, secondHeap, (stage_iff first model.input initial firstHeap x).mp ⟨firstFuel, firstRun⟩,
      (stage_iff second (f.select x model.input) firstHeap secondHeap y).mp ⟨secondFuel, secondRun⟩,
      (stage_iff third (selectThird f g model.input x y) secondHeap final z).mp ⟨thirdFuel, thirdRun⟩⟩
  · rintro ⟨firstHeap, secondHeap, firstRun, secondRun, thirdRun⟩
    obtain ⟨firstFuel, firstRun⟩ := (stage_iff first model.input initial firstHeap x).mpr firstRun
    obtain ⟨secondFuel, secondRun⟩ := (stage_iff second (f.select x model.input) firstHeap secondHeap y).mpr secondRun
    obtain ⟨thirdFuel, thirdRun⟩ := (stage_iff third (selectThird f g model.input x y) secondHeap final z).mpr thirdRun
    obtain ⟨pairFuel, pairRun⟩ :=
      (Linked.MemRef.returns_iff_stages first second f model.input ⟨initial⟩ x y ⟨secondHeap⟩).mpr
        ⟨firstFuel, secondFuel, ⟨firstHeap⟩, firstRun, secondRun⟩
    exact ⟨pairFuel, thirdFuel, ⟨secondHeap⟩, pairRun, thirdRun⟩

theorem no_return_iff_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (f : Boundary.Wiring P.args Q.args) (g : Boundary.Wiring Q.args R.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    (∀ fuel, runFuel first second third f g model.input fuel ⟨initial⟩ = none) ↔
      ∀ raw, ¬ (Triple.lower first second third f g).Returns (thetaRuntime model.cells)
        (encodeInput initial model.input) raw := by
  constructor
  · intro absent raw returned
    obtain ⟨⟨x, y, z, final⟩, rfl⟩ := (Triple.resultCodec model.cells).surjective raw
    obtain ⟨fuel, success⟩ := (returns_iff_numbered first second third f g model initial final x y z).mpr returned
    rw [absent fuel] at success
    cases success
  · intro absent fuel
    cases returned : runFuel first second third f g model.input fuel ⟨initial⟩ with
    | none => rfl
    | some out =>
      obtain ⟨x, y, z, ⟨final⟩⟩ := out
      exact False.elim (absent _ ((returns_iff_numbered first second third f g model initial final x y z).mp
        ⟨fuel, returned⟩))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Proofs
