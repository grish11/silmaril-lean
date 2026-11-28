module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Provider.Thms

/-! Checked demand receipts for the two numbered layouts of an allocating λ. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered (linkedLambda)
open Isomorphism.RecursiveCall.Numbered.Prefix (AllocatingClient Table)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {actions : Actions m σ}
variable {imports : Ports (Ty V S)} {value : ValueSort V S} {fn : Function V S}
variable {table : MemberSummaries V S} {shifted : Bool}

/-- A typed instance of the existing allocating numbered shape. The λ
retains the shared demand code and its actual capture wires. -/
structure AllocationPlan (Op : Dialect.{u, v} (ValueSort V S) S)
    (table : MemberSummaries V S) (imports : Ports (Ty V S)) (fn : Function V S)
    (value : ValueSort V S) (shifted : Bool) where
  init : DeltaTerm Op imports (if shifted then [[]] else []) value
  binding : Binding Op table imports ((if shifted then [[]] else []) ++ [[.value (.global value)]]) fn

namespace AllocationPlan

variable (plan : AllocationPlan Op table imports fn value shifted)

def numbered : AllocatingClient Op imports fn value shifted :=
  ⟨plan.init.toGraph, plan.binding.term.toGraph⟩

def linkDelta (actions : Actions m σ) (unit : Nat) (inputs : Tuple m.Val imports) (store : σ) :
    Outcome m σ [.value (.global value)] :=
  Executable.linkVertex actions unit inputs (AllocatingClient.initialLocals m shifted)
    (.delta plan.numbered.initializer) store

abbrev Initialized (actions : Actions m σ) (unit : Nat) (inputsL inputsR : Tuple m.Val imports)
    (store : σ) :=
  LinkedRows (plan.linkDelta actions unit inputsL store) (plan.linkDelta actions unit inputsR store)

/-- Initializer and outer wires at another numbered placement of the same λ body. -/
structure Layout (shifted' : Bool) where
  init : DeltaTerm Op imports (if shifted' then [[]] else []) value
  captures : Wires imports ((if shifted' then [[]] else []) ++ [[.value (.global value)]]) plan.binding.context

def withLayout {shifted' : Bool} (other : plan.Layout shifted') :
    AllocationPlan Op table imports fn value shifted' :=
  ⟨other.init, plan.binding.withCaptures other.captures⟩

end AllocationPlan

/-- Reconstruct the physical prefix of the chosen numbered layout. The empty
φ contributes no callable slot. -/
def allocationScope (dispatch : Dispatch actions table) (shifted : Bool) : Scope m :=
  ⟨if shifted then [[]] else [], table, AllocatingClient.initialLocals m shifted,
    AllocatingClient.initialLocals m shifted, dispatch.left, dispatch.right⟩

def allocationChecked (dispatch : Dispatch actions table) (shifted : Bool) :
    (allocationScope dispatch shifted).Checked actions :=
  ⟨⟨dispatch, Table.empty _ (AllocatingClient.initialLocals m shifted),
    Table.empty _ (AllocatingClient.initialLocals m shifted)⟩, rfl, rfl⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
