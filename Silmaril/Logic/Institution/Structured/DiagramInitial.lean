module

public import Silmaril.Logic.Institution.Pi.Defs
public import Mathlib.CategoryTheory.PEmpty
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.CoDiagram
open CategoryTheory CategoryTheory.Limits
universe u v w x
variable (C : Type w) [Category.{x} C]

/-- The empty structured signature needs no object of the underlying category. -/
def empty : CoDiagram.{u,u} C :=
  ⟨Discrete PEmpty, Functor.empty C⟩

/-- The unique map from the empty diagram. -/
def emptyTo (D : CoDiagram.{u,u} C) : empty C ⟶ D where
  Φ := Functor.empty D.Sign
  ρ := { app := fun node => nomatch node.as }

/-- The varying-shape diagram category always has an initial object, even when
its value category has no objects. This is the empty-diagram case of paper §3. -/
def emptyIsInitial : IsInitial (empty.{u} C) :=
  IsInitial.ofUniqueHom (emptyTo C) (by
    intro D f
    have hΦ : f.Φ = (emptyTo C D).Φ := by
      apply Functor.ext
      · intro node
        exact nomatch node.as
      · intro node
        exact nomatch node.as
    apply Diagram.CoHom.ext (f := f) (g := emptyTo C D) hΦ
    apply NatTrans.ext
    funext node
    exact nomatch node.as)

end Silmaril.Logic.Institution.CoDiagram
