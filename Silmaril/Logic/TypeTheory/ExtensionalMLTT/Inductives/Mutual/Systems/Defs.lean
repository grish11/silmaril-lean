module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Systems
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Indexed.Systems.Thms

@[expose] public section

/-! # Fixed-stage institutions and logical maps for the mutual rule presentation

Source annotations are bounded separately from the full W elaboration. Models
are the existing actual finite towers; their source interpretation is the W
interpretation of the explicit elaboration. The proof maps compile actual
source rules and retain exact theory images.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Finite

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory
open Silmaril.Logic.SetTheory

universe u

abbrev Sentence (levels : ℕ) := {j : Judgment // j.UsesBelow levels}

def room (levels : ℕ) : Room.{0, u + 1, u + 1} where
  Sen := Sentence levels
  Mod := Cat.of (Discrete (FiniteTower.{u} levels))
  Sat T j := j.val.encode.ValidIn (Discrete.as T).U

def inst (levels : ℕ) : Discrete Unit ⥤ Room.{0, u + 1, u + 1} :=
  Discrete.functor fun _ => room.{u} levels

/-- Hypothetical consequence uses source theory leaves and ordinary inference;
indexed rules enter as compiled closed-theory contextual derivations. -/
def logic (levels : ℕ) : LogicalSystem.{0, 0, 0, u + 1, u + 1} (Discrete Unit) where
  I := inst.{u} levels
  Derives _ H j := Consequence levels (Subtype.val '' H) j.val
  refl _ j := .hyp ⟨j, Set.mem_singleton j, rfl⟩
  mono := by
    intro S H H' j hsub d
    exact d.mono (Set.image_mono hsub)
  trans := by
    intro S H Δ j hΔ d
    apply d.bind
    rintro q ⟨φ, hφ, rfl⟩
    rcases hφ with hφ | hφ
    · exact .hyp ⟨φ, hφ, rfl⟩
    · exact hΔ φ hφ
  map_derives := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ σ H j d
    rw [Subsingleton.elim σ (𝟙 _), CategoryTheory.Functor.map_id]
    simpa using d

def bundled (levels : ℕ) : Inst.{0, 0, 0, u + 1, u + 1} := (logic.{u} levels).toInst

def encodeSentence (levels : ℕ) (j : Sentence levels) : W.Finite.Sentence levels :=
  ⟨j.val.encode, j.val.encode_usesBelow j.property⟩

/-- Ordinary W sentences are the ordinary part of the explicit mutual source presentation. -/
def ordinarySentence (levels : ℕ) (j : W.Finite.Sentence levels) : Sentence levels :=
  ⟨.ordinary j.val, by simpa [Judgment.UsesBelow, Judgment.universeBound,
    Judgment.annotationBound, Judgment.toIndexed, Indexed.Judgment.universeBound,
    Indexed.Judgment.annotationBound, Indexed.Judgment.encode, W.Jdg.UsesBelow] using j.property⟩

def indexedSentence (levels : ℕ) (j : Sentence levels) : Indexed.Finite.Sentence levels :=
  ⟨j.val.toIndexed, j.val.toIndexed_usesBelow j.property⟩

def indexedCorridor (levels : ℕ) : room.{u} levels ⟶ Indexed.Finite.room.{u} levels where
  sen := indexedSentence levels
  mod := 𝟭 _
  sat _ _ := Iff.rfl

def toIndexed (levels : ℕ) : Inst.CoHom (bundled.{u} levels) (Indexed.Finite.bundled.{u} levels) where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => indexedCorridor levels

/-- Simultaneous proof compilation also lands in the explicit indexed system. -/
def toIndexedLogical (levels : ℕ) :
    LogicalSystem.CoHom (logic.{u} levels) (Indexed.Finite.logic.{u} levels) where
  Φ := 𝟭 _
  ρ := (toIndexed levels).ρ
  map_derives := by
    intro S H j d
    change Set (Sentence levels) at H
    change Sentence levels at j
    change Consequence levels (Subtype.val '' H) j.val at d
    change Indexed.Consequence levels (Subtype.val '' (indexedSentence levels '' H)) _
    have hi : Subtype.val '' (indexedSentence levels '' H) = Judgment.toIndexed '' (Subtype.val '' H) := by
      simp only [← Set.image_comp]
      rfl
    rw [hi]
    exact d.compileIndexed

def encodeCorridor (levels : ℕ) : room.{u} levels ⟶ W.Finite.room.{u} levels where
  sen := encodeSentence levels
  mod := 𝟭 _
  sat _ _ := Iff.rfl

def ordinaryCorridor (levels : ℕ) : W.Finite.room.{u} levels ⟶ room.{u} levels where
  sen := ordinarySentence levels
  mod := 𝟭 _
  sat _ _ := Iff.rfl

def toW (levels : ℕ) : Inst.CoHom (bundled.{u} levels) (W.Finite.bundled.{u} levels) where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => encodeCorridor levels

def fromW (levels : ℕ) : Inst.CoHom (W.Finite.bundled.{u} levels) (bundled.{u} levels) where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => ordinaryCorridor levels

/-- Every source mutual rule and theory leaf compiles at the unchanged fixed stage. -/
def toWLogical (levels : ℕ) :
    LogicalSystem.CoHom (logic.{u} levels) (W.Finite.logic.{u} levels) where
  Φ := 𝟭 _
  ρ := (toW levels).ρ
  map_derives := by
    intro S H j d
    change Set (Sentence levels) at H
    change Sentence levels at j
    change Consequence levels (Subtype.val '' H) j.val at d
    change W.Ctx.JEqB levels (Subtype.val '' (encodeSentence levels '' H)) _ _ _ _
    have hi : Subtype.val '' (encodeSentence levels '' H) = Judgment.encode '' (Subtype.val '' H) := by
      simp only [← Set.image_comp]
      rfl
    rw [hi]
    exact d.compile

/-- Inverse on ordinary W syntax, without an independent primitive indexed syntax claim. -/
def fromWLogical (levels : ℕ) :
    LogicalSystem.CoHom (W.Finite.logic.{u} levels) (logic.{u} levels) where
  Φ := 𝟭 _
  ρ := (fromW levels).ρ
  map_derives := by
    intro S H j d
    change Set (W.Finite.Sentence levels) at H
    change W.Finite.Sentence levels at j
    change W.Ctx.JEqB levels (Subtype.val '' H) _ _ _ _ at d
    change Consequence levels (Subtype.val '' (ordinarySentence levels '' H)) (.ordinary j.val)
    apply Consequence.ordinary
    simpa [Set.image_image, ordinarySentence, Judgment.encode] using d

/-- Include source annotations and elaborated judgments in a larger finite stage. -/
def includeSentence {n m : ℕ} (h : n ≤ m) (j : Sentence n) : Sentence m :=
  ⟨j.val, j.property.trans h⟩

def inclusionCorridor {n m : ℕ} (h : n ≤ m) : room.{u} n ⟶ room.{u} m where
  sen := includeSentence h
  mod := W.Finite.modelReduct h
  sat _ _ := Iff.rfl

def inclusion {n m : ℕ} (h : n ≤ m) : Inst.CoHom (bundled.{u} n) (bundled.{u} m) where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => inclusionCorridor h

/-- Count inclusions preserve the source derivation relation as well as model satisfaction. -/
def inclusionLogical {n m : ℕ} (h : n ≤ m) :
    LogicalSystem.CoHom (logic.{u} n) (logic.{u} m) where
  Φ := 𝟭 _
  ρ := (inclusion h).ρ
  map_derives := by
    intro S H j d
    change Set (Sentence n) at H
    change Sentence n at j
    change Consequence n (Subtype.val '' H) j.val at d
    change Consequence m (Subtype.val '' (includeSentence h '' H)) j.val
    have hi : Subtype.val '' (includeSentence h '' H) = Subtype.val '' H := by
      rw [← Set.image_comp]
      rfl
    rw [hi]
    exact d.include h

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Finite
