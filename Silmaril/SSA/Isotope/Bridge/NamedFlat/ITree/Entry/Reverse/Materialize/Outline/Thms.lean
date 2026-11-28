module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Outline.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Outline.Typed
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Outline.Tree

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open SSA.FiniteSum (append)

universe u v w x
variable {F : Type v} {blocks exits n : Nat} {g : FiniteCFG F blocks exits n}

section Typing

variable {τ : Type u} [TypeFormers τ] [HasTy F τ]
  {β : BoundCtx τ n} {R : Fin blocks → τ} {D : Fin exits → τ}

/-- Exact source typing supplies the discriminator and arm types at the
selected written row. -/
theorem selection_typed (s : Selection g) (typed : g.HasType β R D) :
    ∃ left right, s.arm.HasType β (append R D) (R s.selected) left right :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline.selection_typed s typed

/-- The outline preserves the caller context, old packet types and ordered
outward interface. Only the fresh arrival receives a product parameter. -/
theorem graph_hasType (s : Selection g) (typed : g.HasType β R D) {left right : τ}
    (arm : s.arm.HasType β (append R D) (R s.selected) left right) :
    (graph s).HasType β (s.packetTypes R left right) D :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline.graph_hasType s typed arm

/-- Each pass preserves the exact interface of its source, including
the first appended packet when typing the second outline. -/
theorem TwoArms.hasType (s : TwoArms g) (typed : g.HasType β R D) {left right left' right' : τ}
    (first : s.first.arm.HasType β (append R D) (R s.first.selected) left right)
    (second : s.second.arm.HasType β
      (append (s.first.packetTypes R left right) D)
      (s.first.packetTypes R left right s.second.selected) left' right') :
    (graph s.second).HasType β
      (s.second.packetTypes (s.first.packetTypes R left right) left' right') D :=
  graph_hasType s.second (graph_hasType s.first typed first) second

end Typing

/-- Group the fresh silent transfer with its selecting row. Weak execution
has the original requests, reply continuations, and relative exit labels. -/
theorem graph_tree {Events : Type w → Type w} {α : Type x}
    (s : Selection g) (raw : Primitive Events F α) (env : Env α) :
    region raw env (graph s).erase = region raw env g.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline.graph_tree raw env s

/-- The two actual outlining passes compose at the same caller environment. -/
theorem TwoArms.graph_tree {Events : Type w → Type w} {α : Type x}
    (s : TwoArms g) (raw : Primitive Events F α) (env : Env α) :
    region raw env (graph s.second).erase = region raw env g.erase :=
  (Outline.graph_tree s.second raw env).trans (Outline.graph_tree s.first raw env)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline
