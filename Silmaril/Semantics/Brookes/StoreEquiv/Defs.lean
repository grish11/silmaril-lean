module

public import Silmaril.Semantics.Brookes.Defs
public import Mathlib.Logic.Equiv.Defs

/-! Relabeling both stores in each transition of a Brookes word. -/

@[expose] public section

namespace Silmaril.Semantics.Brookes

variable {S T A : Type*}

/-- Apply a store map to both endpoints of every transition. -/
def Trace.mapStores (f : S → T) (word : Trace S) : Trace T :=
  word.map fun (s, t) => (f s, f t)

/-- Transport completed words along a store equivalence, keeping replies. -/
def Behavior.transport (e : S ≃ T) (behavior : Behavior S A) : Behavior T A :=
  generate fun word result =>
    ∃ source, behavior.accepts source result ∧ Trace.mapStores e source = word

end Silmaril.Semantics.Brookes
