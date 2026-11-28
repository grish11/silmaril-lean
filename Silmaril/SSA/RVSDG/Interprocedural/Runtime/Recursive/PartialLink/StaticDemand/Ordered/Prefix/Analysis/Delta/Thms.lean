module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Delta.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered.Prefix (linkTerm_bind)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports : Ports (Ty V S)} {value : ValueSort V S}
variable {actions : Actions m σ} {unitId : Nat}
variable {inputsL inputsR : Tuple m.Val imports} {initial : σ}
variable {init : DeltaTerm Op imports [] value}
variable {summary : MemberSummary V S} {sigs : List (Ports (Ty V S))}

/-- Advance one side of the numbered linker from an actual successful
vertex outcome. The same equation applies before and after callable bindings. -/
theorem link_step {past : List (Ports (Ty V S))} {ports outs : Ports (Ty V S)}
    (inputs : Tuple m.Val imports) (locals : Locals m.Val past) (node : VertexTerm Op imports past ports)
    (tail : ModuleTerm Op imports (past ++ [ports]) sigs outs)
    {values : Tuple m.Val ports} {store : σ}
    (ran : Executable.linkVertex actions unitId inputs locals node.toGraph initial = .linked values store) :
    Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs locals (.bind node tail) initial =
      Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs (locals.snoc values) tail store := by
  refine (linkTerm_bind actions unitId inputs locals node tail initial).trans ?_
  simp only [ran]

theorem link_delta {outs : Ports (Ty V S)} (inputs : Tuple m.Val imports)
    (tail : ModuleTerm Op imports [[.value (.global value)]] sigs outs)
    {values : Tuple m.Val [.value (.global value)]} {store : σ}
    (ran : Executable.linkVertex (past := []) actions unitId inputs PUnit.unit (.delta init.toGraph) initial =
      .linked values store) :
    Executable.link actions unitId (OmegaTerm.toGraph ⟨.bind (.delta init) tail⟩) inputs initial =
      Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm (past := [[.value (.global value)]])
      actions unitId inputs (values, PUnit.unit) tail store :=
  link_step (past := []) inputs PUnit.unit (.delta init) tail ran

/-- Analyze a numbered δ→λ/φ module from a checked initializer receipt.
The existing walk starts with the actual initialized locals and common
store, and the receipt relates its result to the original numbered link. -/
def Plan.analyzeNumberedAfterDelta
    (graph : Omega Op imports [summary.fn.port] ([.value (.global value)] :: sigs))
    (receipt : DeltaPrefix actions unitId init inputsL inputsR initial)
    {tail : ModuleTerm Op imports [[.value (.global value)]] sigs [summary.fn.port]}
    (plan : Plan inputsL inputsR receipt.scope summary tail)
    (source : graph.toTerm = ⟨.bind (.delta init) tail⟩) :
    Option (ExportAnalysis actions summary (Executable.link actions unitId graph inputsL initial)
      (Executable.link actions unitId graph inputsR initial)) :=
  let same := graph.toGraph_toTerm.symm.trans (congrArg OmegaTerm.toGraph source)
  let left := (congrArg (fun g => Executable.link actions unitId g inputsL initial) same).trans
    (link_delta inputsL tail receipt.linkedL)
  let right := (congrArg (fun g => Executable.link actions unitId g inputsR initial) same).trans
    (link_delta inputsR tail receipt.linkedR)
  (plan.walk actions unitId inputsL inputsR receipt.store receipt.checked).map fun linked =>
    ⟨linked.relink left right, plan.problem, plan.mem_problem_iff⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
