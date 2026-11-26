module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Support.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Typed
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Tree

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize

open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)

universe u v w x
variable {F : Type v} {labels blocks exits n : Nat}

/-- The inserted binder has the exact type of the evaluated operand. -/
theorem graph_hasType {τ : Type u} [TypeFormers τ] [HasTy F τ]
    {β : BoundCtx τ n} {R : Fin blocks → τ} {D : Fin exits → τ}
    {g : FiniteCFG F blocks exits n} (typed : g.HasType β R D) :
    (graph g).HasType β R D :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.graph_hasType typed

/-- Scoping is preserved at the original value bound, including packet-only scope. -/
theorem body_scoped (t : Flat F labels n) (canBind : Bool) {bound : Nat}
    (s : t.erase.Scoped labels bound) : (body canBind t).erase.Scoped labels bound :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.body_scoped t canBind s

/-- Keep the evaluation order of the let and its continuation. Alias
contraction in an arm only eliminates a variable lookup. -/
theorem graph_tree {Events : Type w → Type w} {α : Type x}
    (raw : Primitive Events F α) (g : FiniteCFG F blocks exits n) (env : Env α) :
    region raw env (graph g).erase = region raw env g.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.graph_tree raw g env

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize
