module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Synthesis.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Proofs

open NestedTheta.Liveness (Demand)

universe u
variable {V S : Type u} {earlier shape : MemberSummaries V S}

theorem append_reads_mono {low high : MemberTransfer shape.members.length} (le : low.LE high) :
    ∀ i : Fin (append earlier shape).members.length, ∀ d : Demand,
      (append earlier (shape.withReads low)).live i d ⊆ (append earlier (shape.withReads high)).live i d := by
  refine slotCases earlier shape (result := fun i => ∀ d : Demand,
    (append earlier (shape.withReads low)).live i d ⊆ (append earlier (shape.withReads high)).live i d) ?_ ?_
  · intro j d
    simp only [append, MemberSummaries.withReads, slotCases_left]
    exact fun _ h => h
  · intro j d
    simpa only [append, MemberSummaries.withReads, slotCases_right] using le j d

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Proofs
