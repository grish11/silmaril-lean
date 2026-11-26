module

public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Signature.Thms
public import Silmaril.Logic.Institution.Pi.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Defs

@[expose] public section

namespace Silmaril.ProofFormats.LeanNDJSON.MLTT

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory
open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Silmaril.Logic.SetTheory

universe u v w

variable {Name : Type}

/-- The Tarskian consequence relation of additional events over a signature. -/
def entailment (S : Signature Name) : ER where
  Sen := Sentence S
  Derives := Derives
  refl s := .hyp ⟨s, Set.mem_singleton s, rfl⟩
  mono h hd := hd.mono (Set.image_mono h)
  trans := derives_cut

/-- Signature extension preserves syntactic consequence. -/
def entailmentFunctor (Name : Type) : Signature Name ⥤ ER where
  obj := entailment
  map f := ⟨Sentence.weaken f, fun {H s} =>
    (derives_weaken_iff f H s).mp⟩
  map_id _ := ER.hom_ext (funext Sentence.weaken_id)
  map_comp f g := ER.hom_ext (funext (Sentence.weaken_comp f g))

/-- The π-institution for any diagram of named declaration signatures. -/
def piOver {J : Type v} [Category.{w} J] (F : J ⥤ Signature Name) : PiCoIns.{v,w,0} :=
  ⟨J, F ⋙ entailmentFunctor Name⟩

/-- The π-institution on all signatures for this type of names. -/
def pi (Name : Type) : PiCoIns.{0,0,0} := piOver (𝟭 (Signature Name))

/-- A model supplies a universe budget and an actual finite tower of that size. -/
structure BudgetModel where
  levels : Nat
  tower : FiniteTower.{u} levels

/-- An event must fit the model's budget and hold under every assignment
satisfying its declaration context in the model's tower. -/
def BudgetModel.Satisfies {S : Signature Name} (M : BudgetModel.{u}) (s : Sentence S) : Prop :=
  s.judgment.UsesBelow M.levels ∧ s.judgment.ValidIn M.tower.U

/-- The ordinary room with models of varying universe bandwidth. -/
def budgetRoom (S : Signature Name) : Room.{0,u + 1,u + 1} where
  Sen := Sentence S
  Mod := Cat.of (Discrete BudgetModel.{u})
  Sat M s := M.as.Satisfies s

/-- Reducts retain the tower. The sentence translation retains its judgment. -/
def budgetFunctor (Name : Type) : Signature Name ⥤ Room.{0,u + 1,u + 1} where
  obj := budgetRoom
  map f := ⟨Sentence.weaken f, 𝟭 _, fun _ _ => Iff.rfl⟩
  map_id _ := Room.hom_ext (funext Sentence.weaken_id) rfl
  map_comp f g := Room.hom_ext (funext (Sentence.weaken_comp f g)) (Functor.id_comp _).symm

/-- The ordinary institution for any diagram of signatures. -/
def budgetOver {J : Type v} [Category.{w} J] (F : J ⥤ Signature Name) :
    Inst.{v,w,0,u + 1,u + 1} where
  Sign := J
  I := F ⋙ budgetFunctor Name

/-- The ordinary institution on all signatures for this type of names. -/
def budget (Name : Type) : Inst.{0,0,0,u + 1,u + 1} where
  Sign := Signature Name
  I := budgetFunctor Name

/-- The fixed-budget slice retains just the sentences that fit the tower. -/
abbrev BoundedSentence (levels : Nat) (S : Signature Name) :=
  {s : Sentence S // s.judgment.UsesBelow levels}

/-- The ordinary room at a fixed universe budget. -/
def fixedRoom (levels : Nat) (S : Signature Name) : Room.{0,u + 1,u + 1} where
  Sen := BoundedSentence levels S
  Mod := (Finite.room.{u} levels).Mod
  Sat M s := (Finite.room.{u} levels).Sat M ⟨s.val.judgment, s.property⟩

/-- The fixed-budget sentence translation. -/
def BoundedSentence.weaken {n : Nat} {S T : Signature Name} (f : S ⟶ T)
    (s : BoundedSentence n S) : BoundedSentence n T :=
  ⟨s.val.weaken f, s.property⟩

/-- The fixed-budget institution on all signatures. -/
def fixedBudget (Name : Type) (levels : Nat) : Inst.{0,0,0,u + 1,u + 1} where
  Sign := Signature Name
  I := {
    obj := fixedRoom levels
    map f := ⟨BoundedSentence.weaken f, 𝟭 _, fun _ _ => Iff.rfl⟩
    map_id _ := Room.hom_ext rfl rfl
    map_comp _ _ := Room.hom_ext rfl (Functor.id_comp _).symm }

/-- At a fixed budget, map events to bounded MLTT judgments. The target has the
same tower models, so this is an ordinary institution comorphism. -/
def toFiniteMLTT (Name : Type) (levels : Nat) :
    Inst.CoHom (fixedBudget.{u} Name levels) (Finite.bundled.{u} levels) where
  Φ := (Functor.const _).obj (Discrete.mk ())
  ρ := {
    app _ := ⟨fun s => ⟨s.val.judgment, s.property⟩, 𝟭 _, fun _ _ => Iff.rfl⟩
    naturality _ _ _ := Room.hom_ext rfl rfl }

end Silmaril.ProofFormats.LeanNDJSON.MLTT
