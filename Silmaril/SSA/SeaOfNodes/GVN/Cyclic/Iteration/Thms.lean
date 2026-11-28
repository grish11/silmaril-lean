module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Correctness
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration

open Activation (Inputs)
open Deletion (DeletedLoop)
open Diamond (Model Signature Ty ValueSort sortValue)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {m : Model.{u,v,w} Op}

section Driver

variable (advance : Step Op inputs carried entrySigs out)

/-- Each one-binding step spends one unit of fuel and accounts for one deletion. -/
theorem runWith_progress
    (shrinks : ∀ {headers} {current : Loop.Graph Op inputs carried entrySigs headers out}
      {next : DeletedLoop Op inputs carried entrySigs out},
        advance current = some next → next.headerSigs.length + 1 = headers.length)
    (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    let result := runWith advance fuel loop
    result.rewrite.headerSigs.length + result.deletions = headerSigs.length ∧ result.deletions ≤ fuel :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.runWith_progress advance shrinks fuel loop

/-- Initial binding count suffices to stop under the supplied shrinking step. -/
theorem runWith_stops_of_fuel
    (shrinks : ∀ {headers} {current : Loop.Graph Op inputs carried entrySigs headers out}
      {next : DeletedLoop Op inputs carried entrySigs out},
        advance current = some next → next.headerSigs.length + 1 = headers.length)
    (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) (enough : headerSigs.length ≤ fuel) :
    advance (runWith advance fuel loop).rewrite.graph = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.runWith_stops advance shrinks fuel loop enough

/-- Agreement at a fixed backedge budget composes across the actual sequence of edits. -/
theorem runWith_evalBackedges (input : Inputs m inputs) (budget : Nat)
    (preserves : ∀ {headers} {current : Loop.Graph Op inputs carried entrySigs headers out}
      {next : DeletedLoop Op inputs carried entrySigs out},
        advance current = some next → next.graph.evalBackedges m budget input = current.evalBackedges m budget input)
    (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    (runWith advance fuel loop).rewrite.graph.evalBackedges m budget input = loop.evalBackedges m budget input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.runWith_eval advance m input budget preserves fuel loop

end Driver

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- The direct-entry driver is the specialization to the original builder. -/
theorem run_eq_runWith (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    run fuel loop = runWith Builder.optimize? fuel loop :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.run_eq_runWith fuel loop

/-- Successful steps account for the exact size change and consume at most the budget. -/
theorem run_progress (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    let result := run fuel loop
    result.rewrite.headerSigs.length + result.deletions = headerSigs.length ∧
      result.deletions ≤ fuel := by
  rw [run_eq_runWith]
  exact runWith_progress Builder.optimize? (fun found => Builder.optimize_count found) fuel loop

/-- One unit of fuel per binding suffices to reach a loop on which the
native step returns `none`. This includes a failed view build. -/
theorem run_stops_of_fuel (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (enough : headerSigs.length ≤ fuel) :
    Builder.optimize? (run fuel loop).rewrite.graph = none := by
  rw [run_eq_runWith]
  exact runWith_stops_of_fuel Builder.optimize? (fun found => Builder.optimize_count found) fuel loop enough

/-- Every iteration budget preserves the evaluator at the same backedge budget. -/
theorem run_evalBackedges (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (input : Inputs m inputs) (budget : Nat) :
    (run fuel loop).rewrite.graph.evalBackedges m budget input = loop.evalBackedges m budget input := by
  rw [run_eq_runWith]
  exact runWith_evalBackedges Builder.optimize? input budget
    (fun found => Builder.optimize_evalBackedges found input budget) fuel loop

/-- Every iteration budget preserves and reflects finite returns. -/
theorem run_finite_returns (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (input : Inputs m inputs) (value : sortValue m.value out) :
    (run fuel loop).rewrite.graph.Returns m input value ↔ loop.Returns m input value := by
  simp only [Loop.Graph.returns_iff_evalBackedges, run_evalBackedges fuel loop input]

/-- The default run preserves every bounded evaluation, including budget exhaustion. -/
theorem normalize_evalBackedges (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (input : Inputs m inputs) (budget : Nat) :
    (normalize loop).rewrite.graph.evalBackedges m budget input = loop.evalBackedges m budget input :=
  run_evalBackedges headerSigs.length loop input budget

/-- The default run preserves and reflects every finite return. -/
theorem normalize_returns (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (input : Inputs m inputs) (value : sortValue m.value out) :
    (normalize loop).rewrite.graph.Returns m input value ↔ loop.Returns m input value :=
  run_finite_returns headerSigs.length loop input value

/-- When a fresh certificate exists for the final loop, its freshly
enumerated proposals contain no accepted shrinking step. -/
theorem normalize_no_candidate (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    {built : Builder.Built (normalize loop).rewrite.graph}
    (admitted : Builder.build? (normalize loop).rewrite.graph = some built) :
    ∀ proposal ∈ Pass.proposals built.view,
      Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.normalize_exhausts loop admitted

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration
