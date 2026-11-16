module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Indexed.Systems.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Semantics.Defs

@[expose] public section

/-! # Hierarchy apex for the indexed derived-rule presentation

The apex retains full unbounded ordinary W inference and the actual compiled
finite-cap indexed rules. It does not extract a common finite cap from an
arbitrary unbounded cofinite derivation. Finite stages are explicitly lifted
to the apex sentence universe before institution maps are constructed.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Indexed.Apex

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory
open WEncoding.Terms

universe u

/-- Hierarchy consequence has genuine ordinary unbounded inference, theory leaves,
and the existing closed-theory indexed derivations at any supplied finite cap. -/
inductive Consequence (H : Set Judgment) : Judgment → Prop where
  | hyp {j} (hj : j ∈ H) : Consequence H j
  | ordinary {j : W.Jdg} (d : W.Ctx.JEqH (Judgment.encode '' H) j.Γ j.A j.a j.b) :
      Consequence H (.ordinary j)
  | indexed {levels : ℕ} {j} (d : Derivation levels j) : Consequence H j

/-- Compilation uses the actual unbounded W proof, forgetting only the finite cap
of a source indexed derivation. -/
theorem Consequence.compile {H : Set Judgment} {j : Judgment} (d : Consequence H j) :
    W.Ctx.JEqH (Judgment.encode '' H) j.encode.Γ j.encode.A j.encode.a j.encode.b := by
  cases d with
  | hyp hj => exact .hyp ⟨_, hj, rfl⟩
  | ordinary d => exact d
  | indexed d => exact d.compile.forget.mono (Set.empty_subset _)

theorem Consequence.bind {H H' : Set Judgment} (f : ∀ j ∈ H, Consequence H' j)
    {j : Judgment} (d : Consequence H j) : Consequence H' j := by
  cases d with
  | hyp hj => exact f _ hj
  | ordinary d =>
      apply Consequence.ordinary
      apply d.bind
      rintro q ⟨p, hp, rfl⟩
      exact (f p hp).compile
  | indexed d => exact .indexed d

theorem Consequence.mono {H H' : Set Judgment} (h : H ⊆ H') {j : Judgment}
    (d : Consequence H j) : Consequence H' j := d.bind fun _ hj => .hyp (h hj)

/-- Actual fixed-stage consequences enter the apex without changing hypotheses or syntax. -/
theorem Consequence.ofFinite {levels : ℕ} {H : Set Judgment} {j : Judgment}
    (d : Indexed.Consequence levels H j) : Consequence H j := by
  cases d with
  | hyp hj => exact .hyp hj
  | ordinary d => exact .ordinary d.forget
  | indexed d => exact .indexed d

/-- The apex is conservative on ordinary unbounded W inference as well. -/
theorem Consequence.ordinary_iff {H : Set W.Jdg} {j : W.Jdg} :
    Consequence (Judgment.ordinary '' H) (.ordinary j) ↔ W.Ctx.JEqH H j.Γ j.A j.a j.b := by
  constructor
  · intro d
    simpa [Set.image_image] using d.compile
  · intro d
    apply Consequence.ordinary
    simpa [Set.image_image] using d

abbrev Sentence := ULift.{u + 1} Judgment

def room : Room.{u + 1, u + 1, u + 1} where
  Sen := Sentence.{u}
  Mod := Cat.of (Discrete SetHierarchy.{u})
  Sat T j := j.down.encode.Valid (Discrete.as T)

def inst : Discrete Unit ⥤ Room.{u + 1, u + 1, u + 1} :=
  Discrete.functor fun _ => room.{u}

def logic : LogicalSystem.{0, 0, u + 1, u + 1, u + 1} (Discrete Unit) where
  I := inst.{u}
  Derives _ H j := Consequence (ULift.down '' H) j.down
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

def bundled : Inst.{0, 0, u + 1, u + 1, u + 1} := logic.{u}.toInst

def encodeSentence (j : Sentence.{u}) : W.Institution.Sentence.{u} := ULift.up j.down.encode

def ordinarySentence (j : W.Institution.Sentence.{u}) : Sentence.{u} := ULift.up (.ordinary j.down)

def encodeCorridor : room.{u} ⟶ W.Institution.room.{u} where
  sen := encodeSentence
  mod := 𝟭 _
  sat _ _ := Iff.rfl

def ordinaryCorridor : W.Institution.room.{u} ⟶ room.{u} where
  sen := ordinarySentence
  mod := 𝟭 _
  sat _ _ := Iff.rfl

def toW : Inst.CoHom bundled.{u} W.Institution.bundled.{u} where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => encodeCorridor

def fromW : Inst.CoHom W.Institution.bundled.{u} bundled.{u} where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => ordinaryCorridor

def toWLogical : LogicalSystem.CoHom logic.{u} W.Institution.logic.{u} where
  Φ := 𝟭 _
  ρ := toW.ρ
  map_derives := by
    intro S H j d
    change Set Sentence.{u} at H
    change Sentence.{u} at j
    change Consequence (ULift.down '' H) j.down at d
    change W.Ctx.JEqH (ULift.down '' (encodeSentence '' H)) _ _ _ _
    have hi : ULift.down '' (encodeSentence '' H) = Judgment.encode '' (ULift.down '' H) := by
      simp only [← Set.image_comp]
      rfl
    rw [hi]
    exact d.compile

def fromWLogical : LogicalSystem.CoHom W.Institution.logic.{u} logic.{u} where
  Φ := 𝟭 _
  ρ := fromW.ρ
  map_derives := by
    intro S H j d
    change Set W.Institution.Sentence.{u} at H
    change W.Institution.Sentence.{u} at j
    change W.Ctx.JEqH (ULift.down '' H) _ _ _ _ at d
    change Consequence (ULift.down '' (ordinarySentence '' H)) (.ordinary j.down)
    apply Consequence.ordinary
    simpa [Set.image_image, ordinarySentence, Judgment.encode] using d

namespace Stage

/-- The same finite source sentences, lifted explicitly to the apex sentence universe. -/
abbrev Sentence (levels : ℕ) := ULift.{u + 1} (Indexed.Finite.Sentence levels)

def room (levels : ℕ) : Room.{u + 1, u + 1, u + 1} where
  Sen := Sentence.{u} levels
  Mod := Cat.of (Discrete (Silmaril.Logic.SetTheory.FiniteTower.{u} levels))
  Sat T j := j.down.val.encode.ValidIn (Discrete.as T).U

def inst (levels : ℕ) : Discrete Unit ⥤ Room.{u + 1, u + 1, u + 1} :=
  Discrete.functor fun _ => room.{u} levels

def logic (levels : ℕ) : LogicalSystem.{0, 0, u + 1, u + 1, u + 1} (Discrete Unit) where
  I := inst.{u} levels
  Derives _ H j := Indexed.Consequence levels ((fun q => q.down.val) '' H) j.down.val
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

def bundled (levels : ℕ) : Inst.{0, 0, u + 1, u + 1, u + 1} := (logic.{u} levels).toInst

/-- Forget the finite sentence bound, retaining its original source judgment. -/
def apexSentence (levels : ℕ) (j : Sentence.{u} levels) : Apex.Sentence.{u} := ULift.up j.down.val

def apexCorridor (levels : ℕ) : room.{u} levels ⟶ Apex.room.{u} where
  sen := apexSentence levels
  mod := Discrete.functor fun T => Discrete.mk (hierarchyFiniteModel T levels)
  sat T j := (W.Jdg.validIn_iff_valid (Discrete.as T) j.down.val.encode).symm

/-- A supplied hierarchy reduces to the actual finite tower needed by the source proof. -/
def toApex (levels : ℕ) : Inst.CoHom (bundled.{u} levels) Apex.bundled.{u} where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => apexCorridor levels

def toApexLogical (levels : ℕ) : LogicalSystem.CoHom (logic.{u} levels) Apex.logic.{u} where
  Φ := 𝟭 _
  ρ := (toApex levels).ρ
  map_derives := by
    intro S H j d
    change Set (Sentence.{u} levels) at H
    change Sentence.{u} levels at j
    change Indexed.Consequence levels ((fun q => q.down.val) '' H) j.down.val at d
    change Apex.Consequence (ULift.down '' (apexSentence levels '' H)) j.down.val
    have hi : ULift.down '' (apexSentence levels '' H) = (fun q : Sentence.{u} levels => q.down.val) '' H := by
      rw [← Set.image_comp]
      rfl
    rw [hi]
    exact Apex.Consequence.ofFinite d

def includeSentence {n m : ℕ} (h : n ≤ m) (j : Sentence.{u} n) : Sentence.{u} m :=
  ULift.up (Indexed.Finite.includeSentence h j.down)

def inclusionCorridor {n m : ℕ} (h : n ≤ m) : room.{u} n ⟶ room.{u} m where
  sen := includeSentence h
  mod := W.Finite.modelReduct h
  sat _ _ := Iff.rfl

def inclusion {n m : ℕ} (h : n ≤ m) : Inst.CoHom (bundled.{u} n) (bundled.{u} m) where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => inclusionCorridor h

def inclusionLogical {n m : ℕ} (h : n ≤ m) :
    LogicalSystem.CoHom (logic.{u} n) (logic.{u} m) where
  Φ := 𝟭 _
  ρ := (inclusion h).ρ
  map_derives := by
    intro S H j d
    change Set (Sentence.{u} n) at H
    change Sentence.{u} n at j
    change Indexed.Consequence n ((fun q => q.down.val) '' H) j.down.val at d
    change Indexed.Consequence m ((fun q => q.down.val) '' (includeSentence h '' H)) j.down.val
    have hi : (fun q => q.down.val) '' (includeSentence h '' H) =
        (fun q : Sentence.{u} n => q.down.val) '' H := by
      rw [← Set.image_comp]
      rfl
    rw [hi]
    exact d.include h

end Stage

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Indexed.Apex
