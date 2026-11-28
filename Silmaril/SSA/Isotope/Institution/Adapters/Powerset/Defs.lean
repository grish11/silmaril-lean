module

public import Silmaril.SSA.Isotope.Institution.Parallel.Inclusions.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.LetSeq.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.LetCase.Thms

/-! # Powerset model restriction for the lower parallel tiers -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.Powerset

open CategoryTheory Semantics Silmaril.Logic.Institution
open Parallel (Tier CaseTypes Control ParOp)
open Parallel.Institution (Equation)

universe u v

variable {τ ε : Type u} {S T : InstrSig τ ε} {D : τ → Type v}

/-- A powerset primitive interpretation, represented by its membership relation.
The value family and the operation for parallel pairing are fixed for a room.
Arrows are the strict arrows with identity computation map. -/
structure Model (D : τ → Type v) (S : InstrSig τ ε) where
  relational : Relational.Model D S

namespace Model

instance : Category (Model D S) where
  Hom X Y := PLift (X = Y)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance (X Y : Model D S) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (PLift (X = Y)))

/-- Use the Mathlib powerset monad and the supplied operation for parallel pairing. -/
abbrev toParallel (pair : ParOp (SetM : Type v → Type v)) (X : Model D S) :
    Parallel.Institution.Model D S where
  M := SetM
  par := pair
  instr := X.relational.toSetModel

/-- Realize each restricted arrow as a strict native arrow. -/
def toParallelFunctor (pair : ParOp (SetM : Type v → Type v)) :
    Model D S ⥤ Parallel.Institution.Model D S where
  obj := toParallel pair
  map f := f.down ▸ 𝟙 _
  map_id _ := rfl
  map_comp f g := by
    cases f.down
    cases g.down
    rfl

/-- Take membership of a computation. Identity computation maps give
inclusions of equal primitive relations. -/
def toRelational : Model D S ⥤ Relational.Model D S where
  obj X := X.relational
  map f := f.down ▸ 𝟙 _
  map_id _ := rfl
  map_comp _ _ := Subsingleton.elim _ _

/-- Signature reduct with the same powerset monad and fixed pairing. -/
def reduct (f : S ⟶ T) (X : Model D T) : Model D S :=
  ⟨X.relational.reduct f⟩

def reductFunctor (f : S ⟶ T) : Model D T ⥤ Model D S where
  obj := reduct f
  map h := ⟨congrArg (reduct f) h.down⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Model

section Rooms

variable {ν : Type u} [DecidableEq ν] {tier : Tier} [HasProduct τ] [HasUnit τ]
  [CaseTypes tier τ] [ProductModel D] [UnitModel D]

/-- The native lower-tier equations interpreted in the fixed powerset profile. -/
def room (h : tier ≠ .iter) (C : Control tier D Id) (Γ : Ctx ν τ)
    (pair : ParOp (SetM : Type v → Type v)) (S : InstrSig τ ε) :
    Room.{u, 0, max u v} where
  Sen := Equation S tier Γ
  Mod := Cat.of (Model D S)
  Sat X φ := φ.Holds (X.toParallel pair) (Parallel.Institution.lowerControl h C SetM)

end Rooms

section Sentences

variable {ν : Type u} [DecidableEq ν] {Γ : Ctx ν τ}

def ofLetSeq [HasProduct τ] [HasUnit τ] (φ : Relational.LetSeq.Sentence S Γ) :
    Equation S .seq Γ :=
  Equation.ofLetSeq φ.2.1.2 φ.2.2.2

def ofLetCase [TypeFormers τ] (φ : Relational.LetCase.Sentence S Γ) :
    Equation S .case Γ :=
  Equation.ofLetCase φ.2.1.2 φ.2.2.2

end Sentences
end Silmaril.Isotope.Institution.Adapters.Powerset
