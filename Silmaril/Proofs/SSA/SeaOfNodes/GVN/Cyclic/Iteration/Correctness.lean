module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration
open Activation (Inputs)
open Deletion (DeletedLoop)
open Diamond (Model Signature Ty ValueSort)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}

section Driver

variable (advance : Step Op inputs carried entrySigs out)

private theorem runWith_none {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
    (fuel : Nat) (found : advance loop = none) :
    runWith advance (fuel + 1) loop = ⟨⟨headerSigs, loop⟩, 0⟩ := by
  simp only [runWith, found]

private theorem runWith_some {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
    (fuel : Nat) {next : DeletedLoop Op inputs carried entrySigs out}
    (found : advance loop = some next) :
    runWith advance (fuel + 1) loop =
      ⟨(runWith advance fuel next.graph).rewrite, (runWith advance fuel next.graph).deletions + 1⟩ := by
  simp only [runWith, found]

variable (shrinks : ∀ {headers} {current : Loop.Graph Op inputs carried entrySigs headers out}
  {next : DeletedLoop Op inputs carried entrySigs out},
    advance current = some next → next.headerSigs.length + 1 = headers.length)
include shrinks

theorem runWith_progress (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    let result := runWith advance fuel loop
    result.rewrite.headerSigs.length + result.deletions = headerSigs.length ∧
      result.deletions ≤ fuel := by
  induction fuel generalizing headerSigs with
  | zero => exact ⟨rfl, Nat.le_refl _⟩
  | succ fuel ih =>
    cases next : advance loop with
    | none => simp [runWith, next]
    | some shortened =>
      have count := shrinks next
      have ⟨exactCount, budget⟩ := ih shortened.graph
      simp only [runWith, next]
      exact ⟨by omega, by omega⟩

theorem runWith_stops (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (enough : headerSigs.length ≤ fuel) :
    advance (runWith advance fuel loop).rewrite.graph = none := by
  induction fuel generalizing headerSigs with
  | zero =>
    change advance loop = none
    cases next : advance loop with
    | none => rfl
    | some shortened =>
      have count := shrinks next
      omega
  | succ fuel ih =>
    cases next : advance loop with
    | none =>
      rw [runWith_none advance fuel next]
      exact next
    | some shortened =>
      have count := shrinks next
      rw [runWith_some advance fuel next]
      exact ih shortened.graph (by omega)

omit shrinks

theorem runWith_eval (m : Model.{u,v,w} Op) (input : Inputs m inputs) (budget : Nat)
    (preserves : ∀ {headers} {current : Loop.Graph Op inputs carried entrySigs headers out}
      {next : DeletedLoop Op inputs carried entrySigs out},
        advance current = some next → next.graph.evalBackedges m budget input = current.evalBackedges m budget input)
    (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    (runWith advance fuel loop).rewrite.graph.evalBackedges m budget input = loop.evalBackedges m budget input := by
  induction fuel generalizing headerSigs with
  | zero => rfl
  | succ fuel ih =>
    cases next : advance loop with
    | none => rw [runWith_none advance fuel next]
    | some shortened =>
      rw [runWith_some advance fuel next]
      exact (ih shortened.graph).trans (preserves next)

end Driver

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

theorem run_eq_runWith (fuel : Nat) (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    run fuel loop = runWith Builder.optimize? fuel loop := by
  induction fuel generalizing headerSigs with
  | zero => rfl
  | succ fuel ih =>
    cases next : Builder.optimize? loop with
    | none => simp only [run, runWith, next]
    | some shortened => simp only [run, runWith, next, ih shortened.graph]

theorem normalize_exhausts (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    {built : Builder.Built (normalize loop).rewrite.graph}
    (admitted : Builder.build? (normalize loop).rewrite.graph = some built) :
    ∀ proposal ∈ Pass.proposals built.view,
      Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal = none := by
  have stopped := runWith_stops Builder.optimize? (fun found => Builder.optimize_count found)
    headerSigs.length loop (Nat.le_refl _)
  rw [← run_eq_runWith] at stopped
  change Builder.optimize? (normalize loop).rewrite.graph = none at stopped
  rw [Builder.optimize?, admitted, Option.bind_some] at stopped
  exact (Pass.step?_eq_none_iff built.view).mp stopped

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration
