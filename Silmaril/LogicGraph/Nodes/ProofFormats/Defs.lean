module

public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Defs

@[expose] public section

namespace Silmaril.LogicGraph.LeanNDJSON

universe u

/-- The named Lean NDJSON fragment at a fixed finite MLTT universe budget. -/
def fixedBudget (levels : Nat) :=
  Silmaril.ProofFormats.LeanNDJSON.MLTT.fixedBudget.{u} Lean.Name levels

end Silmaril.LogicGraph.LeanNDJSON

silmaril institution logic.proof_formats.lean_ndjson.mltt.fixed_budget :=
    Silmaril.LogicGraph.LeanNDJSON.fixedBudget
  (title := "Lean NDJSON declarations in extensional MLTT, at a fixed universe budget")
  (doc := "Named monomorphic declarations with positive sorts, closed successor/max levels, \
    variables, application, lambdas and dependent products. Successful NDJSON import checks \
    format and references. Extensional MLTT typing is a separate obligation. Each sentence's \
    judgment, including its declaration context, must fit the budget. Models are supplied \
    finite ZFSet towers at that height. Satisfaction quantifies over assignments satisfying \
    the event's declaration context. For syntactic consequence, see \
    Silmaril.ProofFormats.LeanNDJSON.MLTT.pi and derives_iff_mltt in the consequence coverage matrix.")
