module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Defs

/-! # The supplied record as an input of the weak-tree model

The arrow of a checked table starts at the product of its captured
context. The supplied input record of an entry has the same fields, as
a value of the packed input type. `packed` is that record as a point of
the product.
-/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceCategorical

open LambdaSSA.Semantics.Categorical (ctxObj)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues typeModel)
open NamedFlat.Entry.Record (Input)

universe u

variable {κ : Type (u + 1)} [AtomValues κ]

attribute [local instance] typeModel

local notation "T" => LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)

/-- The supplied record as a point of the product of the captured
context, field by field. -/
def packed : {n : Nat} → (β : BoundCtx (Ty κ) n) → Input β → ctxObj T β.toList
  | _, .nil, _ => PUnit.unit
  | _, .snoc β _, record => (packed β record.1, record.2)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceCategorical
