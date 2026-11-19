module

public import Silmaril.Semantics.Function.Defs
public import Silmaril.Semantics.Region.Abstract.Named.Defs
public import Silmaril.Semantics.Region.Semantic.Defs

/-! # Interpretation of function candidates

The machine supplies actual steps and a calling convention. A CFG supplies
labels and boundaries, not evidence of an invocation or return. A region
can have a valid first-exit bound without being a function.
-/

@[expose] public section
namespace Silmaril.Semantics.Function
universe u v

structure Machine (sig : Signature.{u}) where
  State : Type v
  Label : Type v
  Event : Type v
  Stop : Type v
  system : sig.Context → Region.TransitionSystem State Label Event Stop
  owner : sig.Context → sig.Internal → State → Prop
  event : sig.Context → State → List Event → State → Edge sig → Prop
  invocation : sig.Context → CallSite sig → Node sig → State → State → Prop
  tailTransfer : sig.Context → CallSite sig → Node sig → State → State → Prop
  returned : sig.Context → sig.Internal → State → State → Prop

variable {sig : Signature.{u}}

/-- A region relation proposes a body by its abstract CFG interface. This
forgets neither the source context nor the function name. It does not
classify invocation, return or tail transfer. -/
def fromRegionView {Label : Type v}
    (region : Region.Abstract.SegmentRegPred sig.Context sig.Internal sig.Body Label (Set Label))
    (view : sig.Context → Graph.CFGLike sig.Body Label) (context : sig.Context) : Decomposition sig :=
  fun name row => region context name row ((view context).entry row) ((view context).exits row)

def Machine.transfer (machine : Machine.{u,v} sig) (context : sig.Context)
    (edge : Edge sig) (pre post : machine.State) : Prop :=
  match edge.origin.transfer with
  | .invoke => machine.invocation context edge.origin edge.callee pre post
  | .tail => machine.tailTransfer context edge.origin edge.callee pre post

def Machine.callStep (machine : Machine.{u,v} sig) (context : sig.Context)
    (edge : Edge sig) (pre post : machine.State) : Prop :=
  machine.owner context edge.origin.caller pre ∧
  ∃ trace, (machine.system context).step pre trace post ∧
    machine.event context pre trace post edge ∧ machine.transfer context edge pre post

def Machine.actualCalls (machine : Machine.{u,v} sig) (context : sig.Context) : Calls sig :=
  fun edge => ∃ pre post, machine.callStep context edge pre post

/-- A profile interprets arbitrary bodies as CFGs, including their admitted
entry states. Neither the callers nor the graph library inspect the machine. -/
structure Boundaries (machine : Machine.{u,v} sig) where
  view : sig.Context → Graph.CFGLike sig.Body machine.Label
  admit : sig.Context → sig.Internal → sig.Body → machine.State → Prop
  formed : sig.Context → machine.Label → Prop

variable {machine : Machine.{u,v} sig}

def Boundaries.RegionValid (boundary : Boundaries machine) (context : sig.Context)
    (name : sig.Internal) (row : sig.Body) : Prop :=
  let view := boundary.view context
  boundary.formed context (view.entry row) ∧ view.entry row ∈ view.internal row ∧
    (∃ state, boundary.admit context name row state) ∧
    (∀ state, boundary.admit context name row state → (machine.system context).pc state = view.entry row) ∧
    (∀ label ∈ view.exits row, boundary.formed context label) ∧
    Region.Sound (machine.system context) (boundary.admit context name row)
      (fun label => label ∈ view.internal row) (fun label => label ∈ view.exits row)

/-- An adapter classifies real first exits, not arbitrary outgoing CFG edges.
Exceptional halts remain separate. A first exit that invokes another function
is not that callee's return. -/
def Boundaries.FunctionExits (boundary : Boundaries machine) (context : sig.Context)
    (name : sig.Internal) (row : sig.Body) : Prop :=
  ∀ initial trace final, boundary.admit context name row initial →
    Region.FirstExit (machine.system context) (fun label => label ∈ (boundary.view context).internal row)
      initial trace final →
    machine.returned context name initial final ∨
    ∃ edge pre, edge.origin.caller = name ∧ machine.callStep context edge pre final ∧
      ∃ earlier last, trace = earlier ++ last ∧
        Region.Inside (machine.system context) (fun label => label ∈ (boundary.view context).internal row)
          initial earlier pre ∧
        (machine.system context).step pre last final ∧ machine.event context pre last final edge

def Boundaries.semanticBodies (boundary : Boundaries machine) (context : sig.Context) :
    Decomposition sig := fun name row =>
  boundary.RegionValid context name row ∧ boundary.FunctionExits context name row

/-- The extraction adapter chooses candidates; the interpretation justifies
the region and function-specific obligations independently. -/
structure Correspondence (boundary : Boundaries machine) (context : sig.Context)
    (candidates : Decomposition sig) (analysis : Analysis sig) : Prop where
  region : ∀ ⦃name row⦄, candidates name row → boundary.RegionValid context name row
  exits : ∀ ⦃name row⦄, candidates name row → boundary.FunctionExits context name row
  coversStep : ∀ ⦃edge pre post⦄, machine.callStep context edge pre post → analysis.may edge

/-- Nonempty state-threaded witnesses. A path in the projected graph need not
have one; even these witnesses need additional inter-call stepping rules to
describe executions with intervening instructions. -/
inductive Consecutive (machine : Machine.{u,v} sig) (context : sig.Context) :
    Node sig → machine.State → Node sig → machine.State → Prop where
  | single {edge pre post} (step : machine.callStep context edge pre post) :
      Consecutive machine context (.localFn edge.origin.caller) pre edge.callee post
  | cons {edge pre mid dest post} (step : machine.callStep context edge pre mid)
      (rest : Consecutive machine context edge.callee mid dest post) :
      Consecutive machine context (.localFn edge.origin.caller) pre dest post

end Silmaril.Semantics.Function
