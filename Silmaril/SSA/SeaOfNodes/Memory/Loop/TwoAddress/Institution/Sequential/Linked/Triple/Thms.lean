module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Correctness
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

/-! Exact observations of one numbered three-θ graph and its linked coloured net. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple

open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

/-- Compare the linked graph's complete partial observation with three
separate runs, each initialized by the previous run's returned packet. -/
theorem observe_eq_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial : Heap model.cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime model.cells)
        (lower first second third firstWiring secondWiring) (encodeInput initial model.input) =
      (numbered first second third firstWiring secondWiring model initial).map (resultCodec model.cells) :=
  Proofs.observe_eq_numbered first second third firstWiring secondWiring model initial

/-- The same observation factors through the actual linked pair's returned
packet and a separate run of the third emitted loop. -/
theorem observe_eq_linked_pair (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial : Heap model.cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime model.cells)
        (lower first second third firstWiring secondWiring) (encodeInput initial model.input) =
      (RuntimeObservation.observe (P := target) (thetaRuntime model.cells)
        (Linked.lower first second firstWiring) (encodeInput initial model.input)).bind fun output =>
        let (firstWord, secondWord, middle) := (Linked.resultCodec model.cells).symm output
        let bank := secondWiring.select secondWord (firstWiring.select firstWord model.input)
        (numberedStage (P := R) (.lower third) ⟨model.cells, bank⟩ middle).map fun (word, final) =>
          resultCodec model.cells (firstWord, secondWord, word, final) :=
  Proofs.observe_eq_linked_pair first second third firstWiring secondWiring model initial

theorem returns_iff_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial : Heap model.cells) (out : Result model.cells) :
    (lower first second third firstWiring secondWiring).Returns (thetaRuntime model.cells)
        (encodeInput initial model.input) (resultCodec model.cells out) ↔
      numbered first second third firstWiring secondWiring model initial = Part.some out :=
  Proofs.returns_iff_numbered first second third firstWiring secondWiring model initial out

/-- Each separately emitted stage has its own finite fuel witness. The
second and third start at the exact complete heaps returned by their predecessors. -/
theorem returns_iff_stages (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial final : Heap model.cells) (firstWord secondWord thirdWord : Word) :
    (lower first second third firstWiring secondWiring).Returns (thetaRuntime model.cells)
        (encodeInput initial model.input) (resultCodec model.cells (firstWord, secondWord, thirdWord, final)) ↔
      ∃ firstHeap secondHeap,
        (Petri.lower first).Returns (thetaRuntime model.cells) (encodeInput initial model.input)
          (encodeResult firstWord firstHeap) ∧
        (Petri.lower second).Returns (thetaRuntime model.cells)
          (encodeInput firstHeap (firstWiring.select firstWord model.input)) (encodeResult secondWord secondHeap) ∧
        (Petri.lower third).Returns (thetaRuntime model.cells)
          (encodeInput secondHeap (secondWiring.select secondWord (firstWiring.select firstWord model.input)))
          (encodeResult thirdWord final) :=
  (returns_iff_numbered first second third firstWiring secondWiring model initial _).trans
    (Proofs.numbered_eq_some_iff first second third firstWiring secondWiring model initial final
      firstWord secondWord thirdWord)

theorem no_returns_iff_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial : Heap model.cells) :
    (∀ raw, ¬ (lower first second third firstWiring secondWiring).Returns (thetaRuntime model.cells)
      (encodeInput initial model.input) raw) ↔
      numbered first second third firstWiring secondWiring model initial = Part.none := by
  rw [Part.eq_none_iff]
  constructor
  · intro absent out observed
    exact absent _ ((returns_iff_numbered first second third firstWiring secondWiring model initial out).mpr
      (Part.eq_some_iff.mpr observed))
  · intro absent raw returned
    obtain ⟨out, rfl⟩ := (resultCodec model.cells).surjective raw
    exact absent out (Part.eq_some_iff.mp
      ((returns_iff_numbered first second third firstWiring secondWiring model initial out).mp returned))

/-- One finite completion from the linked entry marking observes the same
complete result as the three staged observers. -/
theorem finishes_iff_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial : Heap model.cells) (out : Result model.cells) :
    RVSDG.NestedTheta.Petri.Finishes (thetaRuntime model.cells) (lower first second third firstWiring secondWiring)
        (encodeInput initial model.input) (resultCodec model.cells out) ↔
      numbered first second third firstWiring secondWiring model initial = Part.some out :=
  (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).trans
    (returns_iff_numbered first second third firstWiring secondWiring model initial out)

theorem no_finishes_iff_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial : Heap model.cells) :
    (∀ raw, ¬ RVSDG.NestedTheta.Petri.Finishes (thetaRuntime model.cells)
      (lower first second third firstWiring secondWiring) (encodeInput initial model.input) raw) ↔
      numbered first second third firstWiring secondWiring model initial = Part.none :=
  (forall_congr' fun _ => not_congr (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _)).trans
    (no_returns_iff_numbered first second third firstWiring secondWiring model initial)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple
