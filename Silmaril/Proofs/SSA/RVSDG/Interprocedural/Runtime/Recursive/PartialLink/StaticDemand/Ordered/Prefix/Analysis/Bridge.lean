module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Proofs

open Continuation.Partial.Executable (Actions)
open NestedTheta.Liveness (Demand)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports : Ports (Ty V S)} {inputsL inputsR : Tuple m.Val imports}
variable {scope : Scope m} {summary : MemberSummary V S} {sigs : List (Ports (Ty V S))}
variable {actions : Actions m σ} {left right : Outcome m σ [summary.fn.port]}

private theorem binding_problem {fn : Function V S} (binding : Binding Op scope.table imports scope.past fn)
    (demand : Demand) (origin : Address) :
    origin ∈ (binding.body.liveness demand).mayOut 0 ↔ origin ∈ binding.summary.live demand := by
  rw [← binding.body.mem_liveIn_iff]
  exact List.mem_eraseDups

theorem plan_problem {tail : ModuleTerm Op imports scope.past sigs [summary.fn.port]}
    (plan : Plan inputsL inputsR scope summary tail) (demand : Demand) (origin : Address) :
    origin ∈ (plan.problem demand).mayOut 0 ↔ origin ∈ summary.live demand := by
  induction plan with
  | finish binding _ _ => exact binding_problem binding demand origin
  | finishDirect binding => exact binding_problem binding demand origin
  | lambda _ _ _ _ ih => exact ih
  | lambdaDirect _ _ ih => exact ih
  | skipLambda _ _ ih => exact ih

theorem port_agreement (analysis : ExportAnalysis actions summary left right) (demand : Demand)
    (argsL argsR : Tuple m.Val summary.fn.args)
    (captures : ∀ {ty} (p : Port summary.captures ty), analysis.liveCapture demand p = true →
      analysis.linked.capsL.get p = analysis.linked.capsR.get p)
    (formals : ∀ {ty} (p : Port summary.fn.args ty), analysis.liveFormal demand p = true →
      argsL.get p = argsR.get p) :
    InputsAgree (m := m) summary demand (prependContext argsL analysis.linked.capsL)
      (prependContext argsR analysis.linked.capsR) :=
  StaticDemand.Proofs.prepend_agrees (fun i => Address.arg i ∈ summary.live demand)
    analysis.linked.capsL analysis.linked.capsR argsL argsR
    (fun p live => captures p (List.contains_iff_mem.2 (List.mem_eraseDups.2 live)))
    (fun p live => formals p (List.contains_iff_mem.2 (List.mem_eraseDups.2 live)))

private theorem get_map {Ty : Type u} {F : Ty → Type v} {G : Ty → Type w} {ports : Ports Ty}
    (f : ∀ ty, F ty → G ty) (values : Tuple F ports) {ty : Ty} (p : Port ports ty) :
    (values.map f).get p = f ty (values.get p) := by
  induction p with
  | head => cases values; rfl
  | tail _ ih => cases values; exact ih _

private theorem get_identityPort {Ty : Type u} {ports : Ports Ty} {ty : Ty} (p : Port ports ty) :
    (NestedTheta.identityPorts ports).get p = p := by
  induction p with
  | head => rfl
  | tail _ ih => simp only [NestedTheta.identityPorts, Tuple.get, get_map, ih]

theorem substitute_dead_get (analysis : ExportAnalysis actions summary left right)
    (demand : Demand) (args replacements : Tuple m.Val summary.fn.args) {ty : Ty V S}
    (p : Port summary.fn.args ty) :
    (analysis.substituteDeadFormals demand args replacements).get p =
      if analysis.liveFormal demand p then args.get p else replacements.get p := by
  simp only [ExportAnalysis.substituteDeadFormals, get_map, get_identityPort]

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Proofs
