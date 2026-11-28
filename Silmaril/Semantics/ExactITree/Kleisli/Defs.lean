module

public import Silmaril.Semantics.ExactITree.Thms

/-! The action of exact lowering on the existing weak ITree Kleisli categories. -/

@[expose] public section

namespace Silmaril.Elgot.ITree.Exact.Signature.Hom

open CategoryTheory

universe u

variable {S T : Signature.{u}}

/-- Keep value types fixed and lower the returned tree of every Kleisli arrow. -/
def kleisli (f : S ⟶ T) : WeakKleisli S.Event ⥤ WeakKleisli T.Event where
  obj X := .mk _ X.of
  map g := .mk (↾fun x => f.lower (g.of x))
  map_id X := by
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    funext x
    exact f.lower_ret x
  map_comp g h := by
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    funext x
    rw [Kleisli.Type.comp_of_eq_kleisliRight, Kleisli.Type.comp_of_eq_kleisliRight]
    exact f.lower_bind (g.of x) (fun y => h.of y)

end Silmaril.Elgot.ITree.Exact.Signature.Hom
