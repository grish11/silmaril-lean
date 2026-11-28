module

public import Silmaril.Logic.ITree.Institution.Trace.Thms
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Basic

@[expose] public section

namespace Silmaril.Logic.ITree.TraceInstitution

open CategoryTheory Silmaril.Elgot.ITree

universe u w

/-- A reply policy on a fixed state carrier. The pointwise order is inclusion
of permitted request, state, typed reply and successor-state tuples. -/
abbrev Policy (S : Signature.{u}) (X : Type w) := Handler X S.Event

namespace Policy

variable {S T : Signature.{u}} {X : Type w}

/-- Interpret a policy at the prescribed common initial states. -/
def toModel (initial : X → Prop) (policy : Policy S X) : Model.{u, w} S :=
  ⟨X, initial, policy⟩

/-- The existing handler restriction keeps the state carrier fixed. -/
def reduct (f : S ⟶ T) (policy : Policy T X) : Policy S X :=
  f.restrict policy

theorem toModel_reduct (f : S ⟶ T) (initial : X → Prop) (policy : Policy T X) :
    (policy.reduct f).toModel initial = (policy.toModel initial).reduct f := rfl

end Policy
end Silmaril.Logic.ITree.TraceInstitution
