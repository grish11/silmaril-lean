module

import Silmaril.SSA.Peggy.Bridge.IR.Canonical

namespace Silmaril.SSA.Peggy.Bridge.IR.Tests

open CategoryTheory
open PEG.Bridge (TotalModel Ordered valuePorts)
open Silmaril.Logic.Institution (Inst)
open Dialect (FixedSortSignature)
open Silmaril.SSA.RVSDG.MLIR

private inductive Op (Name : Type) : PEG.InstructionSet.{0,0} Unit
  | literal (name : Name) : Op Name [] .count
  | add : Op Name [.count, .count] .count

private def source : FixedSortSignature.{0,0} Unit := ⟨Op Bool⟩
private def target : FixedSortSignature.{0,0} Unit := ⟨Op Unit⟩

-- The signature arrow identifies distinct symbols and keeps the binary profile.
private def collapse : source ⟶ target :=
  FixedSortSignature.ofOpcodeMap fun
    | .literal _ => .literal ()
    | .add => .add

private def sourceModel : TotalModel source.ops where
  carrier _ := Nat
  run
    | .literal flag, .nil => ⟨if flag then 3 else 5⟩
    | .add, .cons x (.cons y .nil) => ⟨x.down + y.down⟩

private def targetModel : TotalModel target.ops where
  carrier _ := Nat
  run
    | .literal _, .nil => ⟨7⟩
    | .add, .cons x (.cons y .nil) => ⟨x.down + y.down⟩

private abbrev inputs : List (PEG.Ty Unit) := [.bool]
private abbrev outputs : List (PEG.Ty Unit) := [.count, .count, .count]
private def sort (i : Fin 4) : PEG.Ty Unit := if i.val = 0 then .bool else .count

private def graph (side : Bool) : PEG.Graph source.ops inputs outputs 4 0 where
  forest := emptyForest
  sort := sort
  node
    | ⟨0, _⟩ => .ofLabel (.param .head) .nil
    | ⟨1, _⟩ => .ofLabel (.op (.literal side)) .nil
    | ⟨2, _⟩ => .ofLabel (.op .add) (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil))
    | ⟨3, _⟩ => .ofLabel .phi (.cons ⟨0, rfl⟩ (.cons ⟨2, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))
    | ⟨i + 4, h⟩ => False.elim (by omega)
  roots := .cons ⟨3, rfl⟩ (.cons ⟨2, rfl⟩ (.cons ⟨3, rfl⟩ .nil))

private def equation : PEG.Bridge.Equation source.ops :=
  ⟨inputs, outputs, 4, 4, graph true, graph false, by decide, by decide⟩

private def image : PEG.Bridge.Equation target.ops := mapPEG collapse equation

private def translated : Silmaril.MLIR.Institution.Equation (PEG.Bridge.signature target.ops) :=
  ((peggyToMLIR Unit).ρ.app target).sen image

-- Exact sentence naturality is available before any model is chosen.
example : image.toRVSDG =
    equation.toRVSDG.map (mapOpcode (FixedSortSignature.opcodeMap collapse)) :=
  translateEquation_map collapse equation

example : translated =
    (((peggyToMLIR Unit).ρ.app source).sen equation).map (mapSymbol collapse) :=
  (congrArg (Regionless.translateEquation (PEG.Bridge.profileMap target.ops))
    (translateEquation_map collapse equation)).trans (translate_regionless_map collapse equation.toRVSDG)

-- A concrete disagreement in the original dialect survives both translations.
private theorem notPeggy : ¬ (toPeggy equation).Holds (toTotalPrimitive sourceModel).val := by
  intro h
  let input : RVSDG.Tuple sourceModel.toRVSDG.Val (valuePorts inputs) := .cons ⟨true⟩ .nil
  have runs := ((peg_rvsdg_satisfaction equation sourceModel).mpr h) input
  have bad : (6 : Nat) = 10 := congrArg (fun xs => (xs.get .head).down) runs
  contradiction

example : ¬ (((peggyToMLIR Unit).ρ.app source).sen equation).Holds sourceModel.toMLIR := by
  intro h
  exact notPeggy ((Inst.CoHom.satisfaction (peggyToMLIR Unit) source sourceModel equation).mp h)

-- The relabelled equations agree in the canonical regionless MLIR evaluator.
private theorem satMLIR : translated.Holds targetModel.toMLIR := by
  intro env i
  rfl

-- Exercise the composed, bundled arrow, including its model pullback.
example : (toPeggy image).Holds (toTotalPrimitive targetModel).val :=
  (Inst.CoHom.satisfaction (peggyToMLIR Unit) target targetModel image).mp satMLIR

example : (peggyToMLIR Unit).ModelExpansive := peggyToMLIR_modelExpansive Unit

example : Silmaril.Inst.Comorphism (mathlibDiscrete (pegPlain Unit)) (mathlibDiscrete (mlirPlain Unit)) :=
  mathlibDiscreteComorphism (peggyToMLIR Unit)

-- A canonical ambient model is obtained by the actual model-restriction corridor.
example :
    ((restrictMLIRModels Unit).ρ.app target).mod.obj (Discrete.mk targetModel) =
      Discrete.mk targetModel.toMLIR := rfl

end Silmaril.SSA.Peggy.Bridge.IR.Tests
