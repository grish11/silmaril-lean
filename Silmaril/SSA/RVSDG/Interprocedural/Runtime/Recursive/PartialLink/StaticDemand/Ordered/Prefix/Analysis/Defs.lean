module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Defs

/-! Shared backward demand for a checked numbered module export. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Liveness (Demand)
open Silmaril.Semantics.Dataflow (GenKill)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports : Ports (Ty V S)} {inputsL inputsR : Tuple m.Val imports}
variable {summary : MemberSummary V S} {actions : Actions m σ}
variable {left right : Outcome m σ [summary.fn.port]}

/-- Select the shared GenKill problem of the final checked binding. -/
def Plan.problem : {scope : Scope m} → {summary : MemberSummary V S} → {sigs : List (Ports (Ty V S))} →
    {tail : ModuleTerm Op imports scope.past sigs [summary.fn.port]} →
    Plan inputsL inputsR scope summary tail → Demand → GenKill Nat Address
  | _, _, _, _, .finish binding _ _ => binding.body.liveness
  | _, _, _, _, .finishDirect binding => binding.body.liveness
  | _, _, _, _, .lambda _ _ _ rest => rest.problem
  | _, _, _, _, .lambdaDirect _ rest => rest.problem
  | _, _, _, _, .skipLambda _ rest => rest.problem
termination_by structural _ _ _ _ plan => plan

/-- The export's shared backward problem and its exact correspondence with
its checked dispatch summary, indexed by the actual link outcomes. -/
structure ExportAnalysis (actions : Actions m σ) (summary : MemberSummary V S)
    (left right : Outcome m σ [summary.fn.port]) where
  linked : Export actions summary left right
  problem : Demand → GenKill Nat Address
  mem_problem : ∀ demand origin, origin ∈ (problem demand).mayOut 0 ↔ origin ∈ summary.live demand

/-- Executable entry facts for the least may solution. Callable dispatch
still uses the checked membership in `linked`. -/
def ExportAnalysis.liveIn (_ : ExportAnalysis actions summary left right) (demand : Demand) : List Address :=
  (summary.live demand).eraseDups

def ExportAnalysis.liveCapture (analysis : ExportAnalysis actions summary left right) (demand : Demand)
    {ty : Ty V S} (p : Port summary.captures ty) : Bool :=
  (analysis.liveIn demand).contains (.arg p.index)

def ExportAnalysis.liveFormal (analysis : ExportAnalysis actions summary left right) (demand : Demand) :
    {ty : Ty V S} → Port summary.fn.args ty → Bool :=
  let live := analysis.liveIn demand
  fun p => live.contains (.arg (summary.captures.length + p.index))

/-- Replace dead formals using a tuple of proposed values at the same typed
ports. The requested demand determines which original values are kept. -/
def ExportAnalysis.substituteDeadFormals (analysis : ExportAnalysis actions summary left right)
    (demand : Demand) (args replacements : Tuple m.Val summary.fn.args) : Tuple m.Val summary.fn.args :=
  let live : {ty : Ty V S} → Port summary.fn.args ty → Bool := analysis.liveFormal demand
  (NestedTheta.identityPorts summary.fn.args).map fun _ p =>
    if live p then args.get p else replacements.get p

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
