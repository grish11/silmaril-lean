module

public import Silmaril.Logic.Fragments.Thms

@[expose] public section
namespace Silmaril.Logic.Fragments
open CategoryTheory Silmaril.Logic.Institution
universe u

/-- Adding syntax leaves the base model category and its arrows unchanged. -/
def Fragment.room (F : Fragment.{u}) (R : Room.{u,u,u}) : Room.{u,u,u} :=
  ⟨F.Form R.Sen, R.Mod, fun M p => F.eval (R.Sat M) p⟩

def Fragment.corridor (F : Fragment.{u}) {R S : Room.{u,u,u}} (c : R ⟶ S) : F.room R ⟶ F.room S :=
  ⟨F.map c.sen, c.mod, fun M p => lift_satisfaction F c M p⟩

/-- Arbitrary typed atoms as an independent base language. In particular
an atom may be an abstract named region judgment with abstract support/exits. -/
structure AtomicSignature where
  Atom : Type u

@[ext] structure AtomicSignature.Hom (A B : AtomicSignature.{u}) where
  atom : A.Atom → B.Atom

instance : Category AtomicSignature.{u} where
  Hom := AtomicSignature.Hom
  id _ := ⟨id⟩
  comp f g := ⟨g.atom ∘ f.atom⟩

abbrev AtomicModel (A : AtomicSignature.{u}) := A.Atom → Prop

def atomicRoom (A : AtomicSignature.{u}) : Room.{u,u,u} :=
  ⟨A.Atom, Cat.of (Discrete (AtomicModel A)), fun M a => Discrete.as M a⟩

def atomicCorridor {A B : AtomicSignature.{u}} (f : A ⟶ B) : atomicRoom A ⟶ atomicRoom B :=
  ⟨f.atom, Discrete.functor fun M => Discrete.mk (M ∘ f.atom), fun _ _ => Iff.rfl⟩

end Silmaril.Logic.Fragments
