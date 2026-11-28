module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Proofs

open RVSDG (Tuple)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Silmaril.MLIR.MemRef (Buffer)

variable {P Q : EntrySignature}

set_option backward.isDefEq.respectTransparency false

theorem returns_iff_numbered (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells)
    (word nextWord : Word) (final : Heap model.cells) :
    (∃ fuel, runFuel first second wiring model.input fuel ⟨initial⟩ = some (word, nextWord, ⟨final⟩)) ↔
      (Linked.lower first second wiring).Returns (thetaRuntime model.cells) (encodeInput initial model.input)
        (resultCodec model.cells (word, nextWord, final)) := by
  rw [returns_iff_stages, Linked.returns_iff_numbered, Sequential.numbered_eq_some_iff]
  let firstProgram := RuntimeRoom.GeneratedProgram.lower first
  let secondProgram := RuntimeRoom.GeneratedProgram.lower second
  let rightModel : EntryModel Q := ⟨model.cells, wiring.select word model.input⟩
  constructor
  · rintro ⟨leftFuel, rightFuel, ⟨middle⟩, left, right⟩
    exact ⟨middle, (firstProgram.memref_returns_iff model ⟨initial⟩ word ⟨middle⟩).mp ⟨leftFuel, left⟩,
      (secondProgram.memref_returns_iff rightModel ⟨middle⟩ nextWord ⟨final⟩).mp ⟨rightFuel, right⟩⟩
  · rintro ⟨middle, left, right⟩
    obtain ⟨leftFuel, leftRun⟩ := (firstProgram.memref_returns_iff model ⟨initial⟩ word ⟨middle⟩).mpr left
    obtain ⟨rightFuel, rightRun⟩ := (secondProgram.memref_returns_iff rightModel ⟨middle⟩ nextWord ⟨final⟩).mpr right
    exact ⟨leftFuel, rightFuel, ⟨middle⟩, leftRun, rightRun⟩

theorem no_return_iff_numbered (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ fuel, runFuel first second wiring model.input fuel ⟨initial⟩ = none) ↔
      ∀ raw, ¬ (Linked.lower first second wiring).Returns (thetaRuntime model.cells) (encodeInput initial model.input) raw := by
  constructor
  · intro absent raw numberedReturn
    obtain ⟨⟨word, nextWord, final⟩, rfl⟩ := (resultCodec model.cells).surjective raw
    obtain ⟨fuel, returned⟩ := (returns_iff_numbered first second wiring model initial word nextWord final).mpr numberedReturn
    rw [absent fuel] at returned
    cases returned
  · intro absent fuel
    cases returned : runFuel first second wiring model.input fuel ⟨initial⟩ with
    | none => rfl
    | some out =>
      obtain ⟨word, nextWord, ⟨final⟩⟩ := out
      exact False.elim (absent _ ((returns_iff_numbered first second wiring model initial word nextWord final).mp
        ⟨fuel, returned⟩))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Proofs
