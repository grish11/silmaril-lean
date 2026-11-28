module

public import Silmaril.LogicGraph.Nodes.Logic.Defs
public import Silmaril.LogicGraph.Nodes.ProofFormats.Defs
public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Thms

@[expose] public section

namespace Silmaril.LogicGraph.LeanNDJSON

open Silmaril.Logic.Institution Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

/-- Forget the event and signature presentation while retaining the bounded MLTT judgment. -/
def toFiniteMLTT (levels : Nat) :
    Inst.CoHom (fixedBudget.{u} levels) (Finite.bundled.{u} levels) :=
  Silmaril.ProofFormats.LeanNDJSON.MLTT.toFiniteMLTT Lean.Name levels

theorem toFiniteMLTT_modelExpansive (levels : Nat) :
    (toFiniteMLTT.{u} levels).ModelExpansive :=
  Silmaril.ProofFormats.LeanNDJSON.MLTT.toFiniteMLTT_modelExpansive Lean.Name levels

end Silmaril.LogicGraph.LeanNDJSON

silmaril comorphism logic.proof_formats.lean_ndjson.mltt.to_finite_mltt :=
    Silmaril.LogicGraph.LeanNDJSON.toFiniteMLTT
  (facts := [Silmaril.LogicGraph.LeanNDJSON.toFiniteMLTT_modelExpansive])
  (title := "Lean NDJSON judgments to finite extensional MLTT at the same universe budget")
  (doc := "Send each event to its bounded MLTT judgment in the event's declaration context. The model map is the identity on the finite towers at this budget.")
