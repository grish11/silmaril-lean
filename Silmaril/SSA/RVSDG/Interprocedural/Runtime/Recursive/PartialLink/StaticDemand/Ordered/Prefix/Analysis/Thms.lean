module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Bridge
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Liveness (Demand)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)}
variable {scope : Scope m} {summary : MemberSummary V S} {sigs : List (Ports (Ty V S))}
variable {inputsL inputsR : Tuple m.Val imports} {actions : Actions m σ}
variable {left right : Outcome m σ [summary.fn.port]}

theorem Plan.mem_problem_iff {tail : ModuleTerm Op imports scope.past sigs [summary.fn.port]}
    (plan : Plan inputsL inputsR scope summary tail) (demand : Demand) (origin : Address) :
    origin ∈ (plan.problem demand).mayOut 0 ↔ origin ∈ summary.live demand :=
  Proofs.plan_problem plan demand origin

/-- Run checked backward demand at the final λ export of a numbered
module. The plan covers the exact source recovered from that module. Its
existing admission checks the actual dispatch and link on both inputs. -/
@[expose] def Plan.analyzeNumbered (family : StaticDemand.Family Op table imports) (actions : Actions m σ)
    (unitId : Nat) (graph : Omega Op imports [summary.fn.port] (memberPorts table.members :: sigs))
    (inputsL inputsR : Tuple m.Val imports) (store : σ)
    {tail : ModuleTerm Op imports [memberPorts table.members] sigs [summary.fn.port]}
    (plan : Plan inputsL inputsR (Scope.seed family inputsL inputsR) summary tail)
    (source : graph.toTerm = ⟨.bind (.phi family.group) tail⟩)
    (readyL : family.Ready (family.captures.read inputsL PUnit.unit))
    (readyR : family.Ready (family.captures.read inputsR PUnit.unit)) :
    Option (ExportAnalysis actions summary (Executable.link actions unitId graph inputsL store)
      (Executable.link actions unitId graph inputsR store)) :=
  let same : graph = seededGraph family tail := graph.toGraph_toTerm.symm.trans (congrArg OmegaTerm.toGraph source)
  (plan.admit family actions unitId inputsL inputsR store readyL readyR).map fun linked =>
    ⟨linked.relink (congrArg (fun g => Executable.link actions unitId g inputsL store) same)
        (congrArg (fun g => Executable.link actions unitId g inputsR store) same),
      plan.problem, plan.mem_problem_iff⟩

/-- Run the same ordered analysis from ordinary imports. The first checked
binding may be a λ or a synthesized φ group. Capture checks still use the
actual typed origin and its membership in the accumulated prefix. -/
@[expose] def Plan.analyzeNumberedFromOrdinary (actions : Actions m σ) (unitId : Nat)
    (graph : Omega Op imports [summary.fn.port] sigs) (inputsL inputsR : Tuple m.Val imports) (store : σ)
    {source : OmegaTerm Op imports [summary.fn.port] sigs}
    (plan : Plan inputsL inputsR (Scope.ordinary m) summary source.region)
    (actual : graph.toTerm = source) :
    Option (ExportAnalysis actions summary (Executable.link actions unitId graph inputsL store)
      (Executable.link actions unitId graph inputsR store)) :=
  let same := graph.toGraph_toTerm.symm.trans (congrArg OmegaTerm.toGraph actual)
  (plan.walk actions unitId inputsL inputsR store (Scope.Checked.ordinary actions)).map fun linked =>
    ⟨linked.relink (congrArg (fun g => Executable.link actions unitId g inputsL store) same)
        (congrArg (fun g => Executable.link actions unitId g inputsR store) same),
      plan.problem, plan.mem_problem_iff⟩

theorem ExportAnalysis.mem_liveIn_iff (analysis : ExportAnalysis actions summary left right)
    (demand : Demand) (origin : Address) :
    origin ∈ analysis.liveIn demand ↔ origin ∈ (analysis.problem demand).mayOut 0 :=
  List.mem_eraseDups.trans (analysis.mem_problem demand origin).symm

/-- Agreement on the public live capture and formal facts suffices for
exact linked stores, typed blocks, and observations after resumption. -/
theorem ExportAnalysis.linked_prefixes_agree {unitId : Nat}
    {graph : Omega Op imports [summary.fn.port] sigs} {initial : σ}
    (analysis : ExportAnalysis actions summary (Executable.link actions unitId graph inputsL initial)
      (Executable.link actions unitId graph inputsR initial))
    (demand : Demand) (fuel after : Nat) (argsL argsR : Tuple m.Val summary.fn.args)
    (captures : ∀ {ty} (p : Port summary.captures ty), analysis.liveCapture demand p = true →
      analysis.linked.capsL.get p = analysis.linked.capsR.get p)
    (formals : ∀ {ty} (p : Port summary.fn.args ty), analysis.liveFormal demand p = true →
      argsL.get p = argsR.get p) :
    ∃ left right,
      Executable.run actions fuel unitId graph inputsL .head argsL initial = .ok left ∧
      Executable.run actions fuel unitId graph inputsR .head argsR initial = .ok right ∧
      PrefixObservationsAgree actions demand after left right :=
  analysis.linked.linked_prefixes_agree demand fuel after unitId graph inputsL inputsR argsL argsR initial
    (Proofs.port_agreement analysis demand argsL argsR captures formals)

theorem ExportAnalysis.substituteDeadFormals_get (analysis : ExportAnalysis actions summary left right)
    (demand : Demand) (args replacements : Tuple m.Val summary.fn.args) {ty : Ty V S}
    (p : Port summary.fn.args ty) :
    (analysis.substituteDeadFormals demand args replacements).get p =
      if analysis.liveFormal demand p then args.get p else replacements.get p :=
  Proofs.substitute_dead_get analysis demand args replacements p

/-- The substituted tuple can drive the actual linked invocation. Live
captures still agree, and resumption uses the same observation contract. -/
theorem ExportAnalysis.linked_substituteDeadFormals {unitId : Nat}
    {graph : Omega Op imports [summary.fn.port] sigs} {initial : σ}
    (analysis : ExportAnalysis actions summary (Executable.link actions unitId graph inputsL initial)
      (Executable.link actions unitId graph inputsR initial))
    (demand : Demand) (fuel after : Nat) (args replacements : Tuple m.Val summary.fn.args)
    (captures : ∀ {ty} (p : Port summary.captures ty), analysis.liveCapture demand p = true →
      analysis.linked.capsL.get p = analysis.linked.capsR.get p) :
    ∃ left right,
      Executable.run actions fuel unitId graph inputsL .head args initial = .ok left ∧
      Executable.run actions fuel unitId graph inputsR .head (analysis.substituteDeadFormals demand args replacements)
        initial = .ok right ∧ PrefixObservationsAgree actions demand after left right :=
  analysis.linked_prefixes_agree demand fuel after args (analysis.substituteDeadFormals demand args replacements)
    captures (fun p live => by rw [analysis.substituteDeadFormals_get, ite_eq_left live])

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
