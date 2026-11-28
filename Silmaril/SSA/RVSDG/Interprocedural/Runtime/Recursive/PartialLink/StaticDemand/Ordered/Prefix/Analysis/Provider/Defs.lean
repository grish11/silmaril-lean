module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Delta.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Import.Allocation.Thms

/-! Import the dispatch of a checked numbered export into a client. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered.Prefix (AllocatingClient)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {actions : Actions m σ}
variable {summary : MemberSummary V S} {left right : Outcome m σ [summary.fn.port]}
variable {extra : Ports (Ty V S)} {value : ValueSort V S} {clientFn : Function V S}

/-- Start the client with the provider's verified summary table and dispatch
before linking any client vertices. -/
def Export.importScope (receipt : Export actions summary left right) : Scope m :=
  ⟨[], prepend summary receipt.earlier, PUnit.unit, PUnit.unit, receipt.dispatch.left, receipt.dispatch.right⟩

def Export.importChecked (receipt : Export actions summary left right) : receipt.importScope.Checked actions :=
  ⟨⟨receipt.dispatch, PUnit.unit, PUnit.unit⟩, rfl, rfl⟩

/-- The unshifted numbered allocating-client shape from the provider API. -/
def Export.clientGraph (receipt : Export actions summary left right)
    (init : DeltaTerm Op (summary.fn.port :: extra) [] value)
    (binding : Binding Op (prepend summary receipt.earlier) (summary.fn.port :: extra)
      [[.value (.global value)]] clientFn) :
    Omega Op (summary.fn.port :: extra) [clientFn.port] (AllocatingClient.sigs clientFn value false) :=
  (AllocatingClient.mk (shifted := false) init.toGraph binding.term.toGraph).toGraph

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
