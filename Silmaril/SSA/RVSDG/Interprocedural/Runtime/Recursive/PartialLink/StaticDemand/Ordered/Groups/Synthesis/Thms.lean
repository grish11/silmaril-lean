module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Synthesis.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Synthesis.Monotone

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness (Demand)

universe u v
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {earlier shape : MemberSummaries V S}
variable {imports : Ports (Ty V S)} {past : List (Ports (Ty V S))}

theorem Ordered.append_reads_mono {low high : MemberTransfer shape.members.length} (le : low.LE high) :
    ∀ i : Fin (Ordered.append earlier shape).members.length, ∀ d : Demand,
      (Ordered.append earlier (shape.withReads low)).live i d ⊆
        (Ordered.append earlier (shape.withReads high)).live i d :=
  Ordered.Proofs.append_reads_mono le

/-- Keep earlier dispatch summaries fixed in each round. Only the later
family supplies candidate rows to the finite solver. -/
def Family.CallTransfer.withEarlier (earlier shape : MemberSummaries V S) : Family.CallTransfer shape where
  signatures := Ordered.append earlier shape
  lift reads :=
    let table := Ordered.append earlier (shape.withReads reads)
    ⟨table.live, table.monotone⟩
  lift_mono := Ordered.append_reads_mono

/-- Close the later family with synthesized summaries. The body table
is exactly the earlier summaries followed by the computed local summaries,
as required by the existing ordered static admission. -/
def Family.Template.admitWithEarlier (template : Family.Template Op shape imports (.withEarlier earlier shape) past)
    (safe : template.ReferenceSafe) :
    Family Op template.summaries imports (Ordered.append earlier template.summaries) past :=
  template.admit safe

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand
