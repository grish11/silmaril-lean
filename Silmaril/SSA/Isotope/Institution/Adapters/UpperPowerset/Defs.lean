module

public import Silmaril.SSA.Isotope.Institution.Adapters.Iteration.Thms
public import Silmaril.SSA.Isotope.Institution.Adapters.Powerset.Thms

/-! # The fixed lawful powerset profile of the native LetParIter institution -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.UpperPowerset

open CategoryTheory Semantics Silmaril.Logic.Institution
open LetIter.ProofRelevant.Semantics (TypeModel TyDen)

universe u v

variable {τ ε : Type u} [TypeFormers τ] [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]
  {S T : InstrSig τ ε}

/-- Upper powerset models retain the native primitive and pure interpretations.
A room fixes the powerset monad, its finite-success iteration, and its pairing. -/
structure Model (S : InstrSig τ ε) where
  instructions : LetIter.ProofRelevant.Semantics.InstructionModel S.Instr τ ε SetM

namespace Model

/-- Arrows are the native strict arrows whose computation map is the identity. -/
instance : Category (Model.{u, v} S) where
  Hom X Y := PLift (X = Y)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance (X Y : Model.{u, v} S) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (PLift (X = Y)))

abbrev toNative (pair : Elgot.ParallelPairing (SetM : Type v → Type v))
    (X : Model.{u, v} S) : LetParIter.Institution.Model.{u, v} S :=
  Iteration.setModel pair X.instructions

/-- Retain the native interpretation, including pure instructions, along each signature map. -/
def reduct (pair : Elgot.ParallelPairing (SetM : Type v → Type v))
    (f : S ⟶ T) (X : Model.{u, v} T) : Model.{u, v} S :=
  ⟨((X.toNative pair).reduct f).instructions⟩

def reductFunctor (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) (f : S ⟶ T) :
    Model.{u, v} T ⥤ Model.{u, v} S where
  obj := reduct pair f
  map h := ⟨congrArg (reduct pair f) h.down⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forget iteration and retain powerset membership with the same fixed pairing. -/
def toCase : Model.{u, v} S ⥤ Powerset.Model (TyDen (τ := τ)) S where
  obj X := ⟨Iteration.setRelations X.instructions⟩
  map h := h.down ▸ 𝟙 _
  map_id _ := rfl
  map_comp _ _ := Subsingleton.elim _ _

/-- Regard the retained powerset membership predicates as primitive relations. -/
def toRelational : Model.{u, v} S ⥤ Relational.Model (TyDen (τ := τ)) S :=
  toCase ⋙ Powerset.Model.toRelational

end Model

/-- The full native LetParIter sentences at a fixed powerset profile. -/
def room (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) (S : InstrSig τ ε)
    (ν : Type u) [DecidableEq ν] : Room.{u, 0, max u v} where
  Sen := LetParIter.Institution.Sentence S ν
  Mod := Cat.of (Model.{u, v} S)
  Sat X φ := LetParIter.Institution.Sat (X.toNative pair) φ

end Silmaril.Isotope.Institution.Adapters.UpperPowerset
