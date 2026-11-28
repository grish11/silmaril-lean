module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Remainder.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Delta.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports outs : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
variable {inputsL inputsR : Tuple m.Val imports} {outL outR : Outcome m σ outs}
variable {actions : Actions m σ} {unitId : Nat} {scope : Scope m}

namespace LinkedRemainder

/-- Begin the suffix certificate at the exact source of the numbered module. -/
def start (actions : Actions m σ) (unitId : Nat) (graph : Omega Op imports outs sigs)
    (inputsL inputsR : Tuple m.Val imports) (initial : σ) {source : OmegaTerm Op imports outs sigs}
    (actual : graph.toTerm = source) :
    LinkedRemainder actions unitId inputsL inputsR
      (Executable.link actions unitId graph inputsL initial) (Executable.link actions unitId graph inputsR initial)
      (Scope.ordinary m) source.region :=
  let same := graph.toGraph_toTerm.symm.trans (congrArg OmegaTerm.toGraph actual)
  ⟨Scope.Checked.ordinary actions, initial,
    congrArg (fun g => Executable.link actions unitId g inputsL initial) same,
    congrArg (fun g => Executable.link actions unitId g inputsR initial) same⟩

/-- The two δ attempts use the current typed locals and common store. -/
abbrev DeltaRows {value : ValueSort V S} (init : DeltaTerm Op imports scope.past value) (store : σ)
    (actions : Actions m σ) (unitId : Nat) (inputsL inputsR : Tuple m.Val imports) :=
  LinkedRows (Executable.linkVertex actions unitId inputsL scope.localsL (.delta init.toGraph) store)
    (Executable.linkVertex actions unitId inputsR scope.localsR (.delta init.toGraph) store)

/-- Advance past a checked δ and preserve the earlier callable dispatch. -/
def addDelta {value : ValueSort V S} {init : DeltaTerm Op imports scope.past value}
    {tail : ModuleTerm Op imports (scope.past ++ [[.value (.global value)]]) sigs outs}
    (current : LinkedRemainder actions unitId inputsL inputsR outL outR scope (.bind (.delta init) tail))
    (rows : DeltaRows (scope := scope) init current.store actions unitId inputsL inputsR) :
    LinkedRemainder actions unitId inputsL inputsR outL outR (scope.addInitialized rows.left rows.right) tail :=
  ⟨current.checked.addInitialized rows.left rows.right, rows.store,
    current.linkL.trans (link_step inputsL scope.localsL (.delta init) tail rows.linkedL),
    current.linkR.trans (link_step inputsR scope.localsR (.delta init) tail rows.linkedR)⟩

/-- Compute the next prefix, rejecting a blocked δ or unequal stores.
The result's scope is indexed by the rows returned by the actual linker. -/
def checkDelta [DecidableEq σ] {value : ValueSort V S} {init : DeltaTerm Op imports scope.past value}
    {tail : ModuleTerm Op imports (scope.past ++ [[.value (.global value)]]) sigs outs}
    (current : LinkedRemainder actions unitId inputsL inputsR outL outR scope (.bind (.delta init) tail)) :
    Option ((rows : DeltaRows (scope := scope) init current.store actions unitId inputsL inputsR) ×
      LinkedRemainder actions unitId inputsL inputsR outL outR (scope.addInitialized rows.left rows.right) tail) :=
  (LinkedRows.check _ _).map fun rows => ⟨rows, current.addDelta rows⟩

/-- Use the existing static group admission for a binding before a later δ. -/
def addGroup {later : MemberSummaries V S}
    {binding : GroupBinding Op later imports scope.past (append scope.table later) scope.past}
    {tail : ModuleTerm Op imports (scope.past ++ [memberPorts later.members]) sigs outs}
    (current : LinkedRemainder actions unitId inputsL inputsR outL outR scope (.bind (.phi binding.term) tail))
    (readyL : binding.family.ReadyWith (binding.read inputsL scope.localsL)
      (scope.guardL.combine (binding.family.guard (binding.read inputsL scope.localsL))))
    (readyR : binding.family.ReadyWith (binding.read inputsR scope.localsR)
      (scope.guardR.combine (binding.family.guard (binding.read inputsR scope.localsR)))) :
    Option (LinkedRemainder actions unitId inputsL inputsR outL outR (scope.addGroup binding inputsL inputsR) tail) :=
  (current.checked.addGroupWithEarlier binding inputsL inputsR readyL readyR).map fun checked =>
    ⟨checked, current.store,
      current.linkL.trans (binding.link_step actions unitId inputsL scope.localsL tail current.store),
      current.linkR.trans (binding.link_step actions unitId inputsR scope.localsR tail current.store)⟩

/-- Finish using the ordinary ordered GenKill walk and its export theorem. -/
def analyze {summary : MemberSummary V S} {left right : Outcome m σ [summary.fn.port]}
    {tail : ModuleTerm Op imports scope.past sigs [summary.fn.port]}
    (current : LinkedRemainder actions unitId inputsL inputsR left right scope tail)
    (plan : Plan inputsL inputsR scope summary tail) :
    Option (ExportAnalysis actions summary left right) :=
  (plan.walk actions unitId inputsL inputsR current.store current.checked).map fun linked =>
    ⟨linked.relink current.linkL current.linkR, plan.problem, plan.mem_problem_iff⟩

end LinkedRemainder

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
