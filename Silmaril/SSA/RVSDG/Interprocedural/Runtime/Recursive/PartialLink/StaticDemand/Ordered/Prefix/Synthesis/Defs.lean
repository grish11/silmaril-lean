module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Synthesis.Thms

/-! Build an ordered group from the summaries already in its typed prefix. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {shape : MemberSummaries V S}
variable {imports : Ports (Ty V S)}

/-- The source of one group. Its local rows start from its own signatures;
calls to earlier bindings use the summary table accumulated by the plan. -/
abbrev Scope.GroupTemplate (scope : Scope m) (shape : MemberSummaries V S) (imports : Ports (Ty V S)) :=
  Family.Template Op shape imports (.withEarlier scope.table shape) scope.past

/-- Solve the local rows and produce the typed input to
`Plan.phiWithEarlier`. That step checks actual capture membership and
installs the dispatch proof for the next group's prefix. -/
def Scope.synthesizeGroup (scope : Scope m) (template : scope.GroupTemplate shape imports)
    (safe : template.ReferenceSafe) :
    GroupBinding Op template.summaries imports scope.past (append scope.table template.summaries) scope.past :=
  GroupBinding.ofFamily (template.admitWithEarlier safe)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
