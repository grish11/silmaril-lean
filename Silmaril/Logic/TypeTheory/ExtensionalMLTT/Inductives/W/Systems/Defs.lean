module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Logic
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Logic
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.SetSemantics.Thms
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.BoundedEmbedding

@[expose] public section

/-! # Base MLTT and its W extension as logical systems

The finite sentence map and the derivation map preserve the same universe count.
The hierarchy institutions use the existing arbitrary-hypothesis calculi. All
model reducts are identities: both languages use the same actual set towers.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

universe u

namespace Institution

/-- Hierarchy-level sentences of the extended language. -/
abbrev Sentence := ULift.{u + 1} Jdg

/-- W judgments interpreted in supplied hierarchy models. -/
def room : Room.{u + 1, u + 1, u + 1} where
  Sen := Sentence.{u}
  Mod := Cat.of (Discrete SetHierarchy.{u})
  Sat T j := j.down.Valid (Discrete.as T)

def inst : Discrete Unit ⥤ Room.{u + 1, u + 1, u + 1} :=
  Discrete.functor fun _ => room.{u}

/-- The ordinary W calculus, with arbitrary judgment hypotheses. -/
def logic : LogicalSystem.{0, 0, u + 1, u + 1, u + 1} (Discrete Unit) where
  I := inst.{u}
  Derives _ H j := Ctx.JEqH (ULift.down '' H) j.down.Γ j.down.A j.down.a j.down.b
  refl _ j := .hyp ⟨j, Set.mem_singleton j, rfl⟩
  mono := by
    intro S H H' j hsub h
    exact h.mono (Set.image_mono hsub)
  trans := by
    intro S H Δ j hΔ h
    apply h.bind
    rintro q ⟨φ, hφ, rfl⟩
    rcases hφ with hφ | hφ
    · exact .hyp ⟨φ, hφ, rfl⟩
    · exact hΔ φ hφ
  map_derives := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ σ H j h
    rw [Subsingleton.elim σ (𝟙 _), CategoryTheory.Functor.map_id]
    simpa using h

def bundled : Inst.{0, 0, u + 1, u + 1, u + 1} := logic.{u}.toInst

end Institution

namespace Embedding

/-- Include a whole bounded sentence without changing its universe count. -/
def finiteSentence (levels : ℕ)
    (j : ExtensionalMLTT.Finite.Sentence levels) : Finite.Sentence levels :=
  ⟨judgment j.val, by simpa only [Jdg.UsesBelow, EJdg.UsesBelow, judgment_universeBound] using j.property⟩

/-- Inclusion of base MLTT judgments into the W institution at a fixed count. -/
def finiteCorridor (levels : ℕ) : ExtensionalMLTT.Finite.room.{u} levels ⟶ Finite.room.{u} levels where
  sen := finiteSentence levels
  mod := 𝟭 _
  sat T j := judgment_validIn (Discrete.as T).U j.val

def finiteInclusion (levels : ℕ) :
    Inst.CoHom (ExtensionalMLTT.Finite.bundled.{u} levels) (Finite.bundled.{u} levels) where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => finiteCorridor levels

/-- The finite institution inclusion preserves inference rules and theory hypotheses. -/
def finiteLogical (levels : ℕ) :
    LogicalSystem.CoHom (ExtensionalMLTT.Finite.logic.{u} levels) (Finite.logic.{u} levels) where
  Φ := 𝟭 _
  ρ := (finiteInclusion levels).ρ
  map_derives := by
    intro S H j d
    change Set (ExtensionalMLTT.Finite.Sentence levels) at H
    change ExtensionalMLTT.Finite.Sentence levels at j
    change ECtx.JEqB levels (Subtype.val '' H) _ _ _ _ at d
    change Ctx.JEqB levels (Subtype.val '' (finiteSentence levels '' H)) _ _ _ _
    have hi : Subtype.val '' (finiteSentence levels '' H) = theory (Subtype.val '' H) := by
      simp only [theory, ← Set.image_comp]
      rfl
    rw [hi]
    exact preserves_bounded d

/-- Include a hierarchy-level base sentence. -/
def hierarchySentence (j : ExtensionalMLTT.Institution.Sentence.{u}) : Institution.Sentence.{u} :=
  ULift.up (judgment j.down)

def hierarchyCorridor : ExtensionalMLTT.Institution.room.{u} ⟶ Institution.room.{u} where
  sen := hierarchySentence
  mod := 𝟭 _
  sat T j := judgment_valid (Discrete.as T) j.down

def hierarchyInclusion :
    Inst.CoHom ExtensionalMLTT.Institution.bundled.{u} Institution.bundled.{u} where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => hierarchyCorridor

/-- The hierarchy inclusion also preserves derivations from arbitrary theories. -/
def hierarchyLogical :
    LogicalSystem.CoHom ExtensionalMLTT.Institution.logic.{u} Institution.logic.{u} where
  Φ := 𝟭 _
  ρ := hierarchyInclusion.ρ
  map_derives := by
    intro S H j d
    change Set ExtensionalMLTT.Institution.Sentence.{u} at H
    change ExtensionalMLTT.Institution.Sentence.{u} at j
    change ECtx.JEqH (ULift.down '' H) _ _ _ _ at d
    change Ctx.JEqH (ULift.down '' (hierarchySentence '' H)) _ _ _ _
    have hi : ULift.down '' (hierarchySentence '' H) = theory (ULift.down '' H) := by
      simp only [theory, ← Set.image_comp]
      rfl
    rw [hi]
    exact preserves d

end Embedding

namespace SetTheoryInterpretation

/-- Realize W judgments in the existing independent language of set constraints. -/
noncomputable def interpret (j : Institution.Sentence.{u}) : ExtensionalMLTT.SetTheoryInterpretation.SetSequent.{u} where
  premise T ρ := j.down.Γ.Sat T ρ
  carrier T ρ := j.down.A.denote T ρ Fin.elim0
  lhs T ρ := j.down.a.denote T ρ Fin.elim0
  rhs T ρ := j.down.b.denote T ρ Fin.elim0

noncomputable def corridor : Institution.room.{u} ⟶ ExtensionalMLTT.SetTheoryInterpretation.room.{u} where
  sen := interpret
  mod := 𝟭 _
  sat _ _ := Iff.rfl

noncomputable def toSetTheory :
    Inst.CoHom Institution.bundled.{u} ExtensionalMLTT.SetTheoryInterpretation.bundled.{u} where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => corridor

end SetTheoryInterpretation

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
