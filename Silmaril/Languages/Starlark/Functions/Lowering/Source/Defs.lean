module

public import Silmaril.Languages.Starlark.Functions.Lowering.Defs
public import Silmaril.Languages.Starlark.Functions.Operational.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State Outcome)

def Scratch (start : Nat) (binding : Binding) : Prop :=
  ∃ index, start ≤ index ∧ binding = temporary index

/-- Scratch writes use the frame's direct bindings and allocate no heap cells. -/
def ScratchFree (state : State) : Prop :=
  ∀ index, state.slots (temporary index) = none

/-- Keep the entire heap, iterator stack and lexical slot map. Ignore only the
direct bindings of compiler scratch names at or above the given offset. -/
structure StateMatch (start : Nat) (source target : State) : Prop where
  heap : source.heap = target.heap
  iterators : source.iterators = target.iterators
  slots : source.slots = target.slots
  bindings : ∀ name, ¬ Scratch start name → source.bindings name = target.bindings name

/-- The same successful value or error, with the exact state after scratch projection. -/
inductive OutcomeMatch (start : Nat) {α : Type} : Outcome α → Outcome α → Prop where
  | ok {value : α} {s t : State} : StateMatch start s t → OutcomeMatch start (.ok value s) (.ok value t)
  | error {error : Lists.Error} {s t : State} :
      StateMatch start s t → OutcomeMatch start (.error error s) (.error error t)

/-- The call-free atoms may refer to any non-scratch binding. -/
inductive AtomSafe : {α : Type} → Lists.Code α → Prop where
  | scalar (value : Starlark.Value) : AtomSafe (.scalar value)
  | builtin (id : Lists.Builtin) : AtomSafe (.builtin id)
  | string (text : String) : AtomSafe (.string text)
  | predeclared (value : Starlark.Value) : AtomSafe (.read (.predeclared value))
  | bound {name : Binding} : ¬ Scratch 0 name → AtomSafe (.read (.bound name))
  | list {values : Lists.Code (List Lists.Value)} : AtomSafe values → AtomSafe (.list values)
  | tuple {values : Lists.Code (List Lists.Value)} : AtomSafe values → AtomSafe (.tuple values)
  | dict {entries : Lists.Code (List Lists.Entry)} : AtomSafe entries → AtomSafe (.dict entries)
  | noEntries : AtomSafe .noEntries
  | entry {entries : Lists.Code (List Lists.Entry)} {key value : Lists.Expr} :
      AtomSafe entries → AtomSafe key → AtomSafe value → AtomSafe (.entry entries key value)
  | empty : AtomSafe .empty
  | cons {head : Lists.Expr} {tail : Lists.Code (List Lists.Value)} :
      AtomSafe head → AtomSafe tail → AtomSafe (.cons head tail)
  | index {receiver index : Lists.Expr} :
      AtomSafe receiver → AtomSafe index → AtomSafe (.index receiver index)
  | slice {operands : Lists.Code (List Lists.Value)} : AtomSafe operands → AtomSafe (.slice operands)
  | compare {op : Lists.ComparisonOp} {left right : Lists.Expr} :
      AtomSafe left → AtomSafe right → AtomSafe (.compare op left right)
  | append {receiver value : Lists.Expr} :
      AtomSafe receiver → AtomSafe value → AtomSafe (.append receiver value)

abbrev coreClosureRuns (program : Program) (available : List DeclarationId) : ClosureRuns available :=
  fun plan state out => Exec program (withoutDeclaration available plan.id) state plan.body out

abbrev Dispatches (program : Program) (available : List DeclarationId) :=
  DispatchesWith program available (coreClosureRuns program available)

abbrev Applies (program : Program) (available : List DeclarationId) :=
  AppliesWith program available (coreClosureRuns program available)

abbrev Admitted := AdmittedWith AtomSafe

abbrev Evaluates (program : Program) (available : List DeclarationId) :=
  EvaluatesWith program available (coreClosureRuns program available) AtomSafe

abbrev EvaluatesMany (program : Program) (available : List DeclarationId) :=
  EvaluatesManyWith program available (coreClosureRuns program available) AtomSafe

namespace Dispatches
export DispatchesWith (reject builtin returned failed)
end Dispatches

namespace Applies
export AppliesWith (expansionError expanded)
end Applies

namespace Admitted
export AdmittedWith (atom list tuple dict index slice call branch logical)
end Admitted

namespace Evaluates
export EvaluatesWith (atom list tuple dict index indexReceiverError slice call callError branch branchError logical shortCircuit logicalError rec)
end Evaluates

namespace EvaluatesMany
export EvaluatesManyWith (empty cons headError tailError rec)
end EvaluatesMany

end Silmaril.Languages.Starlark.Functions.Lowering
