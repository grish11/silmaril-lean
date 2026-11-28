module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Correctness
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

/-! Finite returns and absence of the checked numbered splice and its linked coloured net. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked

open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature}

/-- The actual linked graph has the same complete partial observation as the two separately emitted loops. -/
theorem observe_eq_numbered (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime model.cells) (lower first second wiring)
        (encodeInput initial model.input) =
      (numbered (RuntimeRoom.GeneratedProgram.lower first) (RuntimeRoom.GeneratedProgram.lower second)
        model (fun word => wiring.select word model.input) initial).map (resultCodec model.cells) :=
  Proofs.observe_eq_numbered first second wiring model initial

theorem returns_iff_numbered (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) :
    (lower first second wiring).Returns (thetaRuntime model.cells)
        (encodeInput initial model.input) (resultCodec model.cells out) ↔
      numbered (RuntimeRoom.GeneratedProgram.lower first) (RuntimeRoom.GeneratedProgram.lower second)
        model (fun word => wiring.select word model.input) initial = Part.some out :=
  Proofs.returns_iff_numbered first second wiring model initial out

theorem no_returns_iff_numbered (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ raw, ¬ (lower first second wiring).Returns (thetaRuntime model.cells) (encodeInput initial model.input) raw) ↔
      numbered (RuntimeRoom.GeneratedProgram.lower first) (RuntimeRoom.GeneratedProgram.lower second)
        model (fun word => wiring.select word model.input) initial = Part.none :=
  Proofs.no_returns_iff_numbered first second wiring model initial

/-- One finite linked firing uses the same complete observation as the
two stage completions, each with its own finite witness. -/
theorem finishes_iff_coloured (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) :
    RVSDG.NestedTheta.Petri.Finishes (thetaRuntime model.cells) (lower first second wiring)
        (encodeInput initial model.input) (resultCodec model.cells out) ↔
      coloured (RuntimeRoom.GeneratedProgram.lower first) (RuntimeRoom.GeneratedProgram.lower second)
        model (fun word => wiring.select word model.input) initial = Part.some out :=
  (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).trans
    ((returns_iff_numbered first second wiring model initial out).trans (iff_of_eq
      (congrArg (· = Part.some out) (coloured_eq_numbered _ _ model (fun word => wiring.select word model.input) initial)).symm))

theorem no_finishes_iff_coloured (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ raw, ¬ RVSDG.NestedTheta.Petri.Finishes (thetaRuntime model.cells) (lower first second wiring)
      (encodeInput initial model.input) raw) ↔
      coloured (RuntimeRoom.GeneratedProgram.lower first) (RuntimeRoom.GeneratedProgram.lower second)
        model (fun word => wiring.select word model.input) initial = Part.none :=
  (forall_congr' fun _ => not_congr (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _)).trans
    ((no_returns_iff_numbered first second wiring model initial).trans (iff_of_eq
      (congrArg (· = Part.none) (coloured_eq_numbered _ _ model (fun word => wiring.select word model.input) initial)).symm))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked
