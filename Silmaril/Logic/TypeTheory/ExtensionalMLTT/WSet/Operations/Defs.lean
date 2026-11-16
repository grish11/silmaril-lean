module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet

@[expose] public section

/-! # Constructors and dependent elimination on the actual W carrier set

These operations transport the native W constructor and dependent recursor
through `WSet.equiv`. No assumption about an algebra or its soundness is added.
The branch fibres and all well-founded trees remain unrestricted.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet

universe u v

noncomputable section

/-- The W constructor, returning an element of the encoded carrier set. -/
def sup {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (a : A) (f : B a.val → carrier A B) : carrier A B :=
  equiv A B (.mk a (fun b => (equiv A B).symm (f b)))

/-- The dependent step, reindexed along the equivalence with native trees. -/
def nativeStep {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (C : carrier A B → Sort v)
    (s : ∀ a f, (∀ b, C (f b)) → C (sup a f))
    (a : A) (f : B a.val → Tree A B)
    (ih : ∀ b, C (equiv A B (f b))) : C (equiv A B (.mk a f)) := by
  simpa only [sup, Equiv.symm_apply_apply] using s a (fun b => equiv A B (f b)) ih

/-- Native dependent recursion with its motive reindexed to the set carrier. -/
def nativeRec {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (C : carrier A B → Sort v)
    (s : ∀ a f, (∀ b, C (f b)) → C (sup a f)) : ∀ t : Tree A B, C (equiv A B t) :=
  WType.rec (nativeStep C s)

/-- Dependent W elimination on the encoded carrier, for arbitrary `Sort`-valued motives. -/
def elim {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (C : carrier A B → Sort v)
    (s : ∀ a f, (∀ b, C (f b)) → C (sup a f)) : ∀ t : carrier A B, C t :=
  Equiv.piCongrLeft C (equiv A B) (nativeRec C s)

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet
