module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.Trace.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Coherence.Thms

/-! # The packed selected tree in the coherent trace model -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.Trace

open CategoryTheory
open Silmaril
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
  (signature traceJ traceTypes traceInstructions traceRegionCoherent)
open Paper.WithProjectionReturnsAndUnitEta (denoteArrow)
open Paper.WithProjectionReturnsAndUnitEta.ExitPacking (packArrow)
open Semantics.Categorical (packLabel)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The actual packed elaboration agrees with the selected fold in the
existing trace algebra, using its established region coherence. -/
theorem denote_nested :
    letI := traceInstructions
    let := traceRegionCoherent
    denoteArrow traceJ traceTypes (fun _ _ => ⟨rfl, rfl⟩) (packArrow nested.elaborate.property) =
      nested.targetArrow traceJ traceTypes ≫ traceJ.map (packLabel traceTypes Exits) := by
  let := traceInstructions
  let := traceRegionCoherent
  exact nested.denote_packArrow traceJ traceTypes (fun _ _ => ⟨rfl, rfl⟩)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.Trace
