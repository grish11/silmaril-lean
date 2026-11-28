module

public import Mathlib.Logic.Equiv.List
public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Types.Basic

/-! # Transport across changes of representation -/

@[expose] public section

namespace Silmaril.Reindex

universe u

/-- An arrow of the groupoid of index types and bijections. Composition is
`Equiv.trans`, identity is `Equiv.refl` and inverse is `Equiv.symm`. -/
abbrev Index (I J : Type u) := I ≃ J

/-- The existing Mathlib groupoid of isomorphisms of types. -/
abbrev IndexGroupoid := CategoryTheory.Core (Type u)

open CategoryTheory in
/-- Identify typed reindexings with arrows in the core of `Type`. -/
def indexHom (I J : Type u) :
    Index I J ≃ ((⟨I⟩ : IndexGroupoid) ⟶ (⟨J⟩ : IndexGroupoid)) where
  toFun e := ⟨e.toIso⟩
  invFun f := f.iso.toEquiv
  left_inv _ := rfl
  right_inv _ := Core.hom_ext rfl

/-- The group of reindexings at a fixed index type. -/
abbrev Aut (I : Type u) := Equiv.Perm I

/-- Transport a function by precomposing with the inverse domain map and
postcomposing with the forward codomain map. -/
abbrev function := @Equiv.arrowCongr

/-- Transport a binary relation by pulling both arguments back. -/
def relation {A B C D : Type*} (a : A ≃ C) (b : B ≃ D) (r : A → B → Prop) :
    C → D → Prop :=
  fun x y => r (a.symm x) (b.symm y)

/-- Transport a language of finite lists by renaming each entry. -/
def language {A B : Type*} (e : A ≃ B) (L : List A → Prop) : List B → Prop :=
  fun ys => L ((Equiv.listEquivOfEquiv e).symm ys)

end Silmaril.Reindex
