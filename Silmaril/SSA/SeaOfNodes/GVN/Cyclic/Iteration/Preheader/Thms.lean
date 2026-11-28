module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader

open Activation (Inputs)
open Builder (Built build?)
open Builder.Preheader (Native prepare)
open Diamond (Ty ValueSort sortValue)
open Pure.SubZero (model)
open scoped Pure.WordNormalize

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit}

/-- Every run prefix keeps the original preheader and entry Phi packet.
The input and entry signatures are fixed by the result type. -/
theorem run_entry (fuel : Nat) (loop : Native inputs carried entrySigs headerSigs out) :
    let final := (run fuel loop).rewrite.graph
    final.preheader = loop.preheader ∧ final.phiInputs .entry = loop.phiInputs .entry :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.run_entry fuel loop

/-- Each success removes exactly one binding and spends one unit of fuel. -/
theorem run_progress (fuel : Nat) (loop : Native inputs carried entrySigs headerSigs out) :
    let final := run fuel loop
    final.rewrite.headerSigs.length + final.deletions = headerSigs.length ∧ final.deletions ≤ fuel :=
  runWith_progress Builder.Preheader.optimize? (fun found => Builder.Preheader.optimize_count found) fuel loop

/-- The initial binding count suffices to exhaust the supported native step. -/
theorem run_stops_of_fuel (fuel : Nat) (loop : Native inputs carried entrySigs headerSigs out)
    (enough : headerSigs.length ≤ fuel) :
    Builder.Preheader.optimize? (run fuel loop).rewrite.graph = none :=
  runWith_stops_of_fuel Builder.Preheader.optimize? (fun found => Builder.Preheader.optimize_count found) fuel loop enough

theorem run_evalBackedges (fuel : Nat) (loop : Native inputs carried entrySigs headerSigs out)
    (input : Inputs model inputs) (budget : Nat) :
    (run fuel loop).rewrite.graph.evalBackedges model budget input = loop.evalBackedges model budget input :=
  runWith_evalBackedges Builder.Preheader.optimize? input budget
    (fun found => Builder.Preheader.optimize_evalBackedges found input budget) fuel loop

theorem normalize_entry (loop : Native inputs carried entrySigs headerSigs out) :
    let final := (normalize loop).rewrite.graph
    final.preheader = loop.preheader ∧ final.phiInputs .entry = loop.phiInputs .entry :=
  run_entry headerSigs.length loop

/-- A fresh call to the native prepare/build/rewrite/restore checker on
the returned graph finds no further accepted step. -/
theorem normalize_stopped (loop : Native inputs carried entrySigs headerSigs out) :
    Builder.Preheader.optimize? (normalize loop).rewrite.graph = none :=
  run_stops_of_fuel headerSigs.length loop (Nat.le_refl _)

/-- The final prepared graph builds, and no proposal in that view's list
passes the shrinking check at the computed stable partition. -/
theorem normalize_saturated (loop : Native inputs carried entrySigs headerSigs out) :
    let prepared := prepare (normalize loop).rewrite.graph
    ∃ built : Built prepared, build? prepared = some built ∧
      ∀ proposal ∈ Pass.proposals built.view,
        Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.normalize_saturated loop

theorem normalize_evalBackedges (loop : Native inputs carried entrySigs headerSigs out)
    (input : Inputs model inputs) (budget : Nat) :
    (normalize loop).rewrite.graph.evalBackedges model budget input = loop.evalBackedges model budget input :=
  run_evalBackedges headerSigs.length loop input budget

theorem normalize_returns (loop : Native inputs carried entrySigs headerSigs out)
    (input : Inputs model inputs) (value : sortValue model.value out) :
    (normalize loop).rewrite.graph.Returns model input value ↔ loop.Returns model input value := by
  simp only [Loop.Graph.returns_iff_evalBackedges, normalize_evalBackedges loop input]

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader
