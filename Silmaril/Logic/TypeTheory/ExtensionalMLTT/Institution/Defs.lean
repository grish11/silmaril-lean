module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Derivation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetSemantics
public import Silmaril.Logic.Institution.Metatheory.Entailment
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-!
# MLTT and semantic set constraints as institutions

The first institution fixes the language and varies its set-universe hierarchy.
Its sentences are judgment hypotheses and conclusions. The second admits general
set constraints with an environmental premise, two values and a carrier set.
The interpretation translates an MLTT judgment into such a constraint.

Both have one signature. Named declarations, signature extension and translations
to first-order ZF/ZFC formulas are separate extensions.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

universe u

namespace Institution

/-- A lift keeps judgments and semantic constraints in the same sentence universe. -/
abbrev Sentence := ULift.{u + 1} EJdg

/-- The room of MLTT judgments and set hierarchies. -/
def room : Room.{u + 1, u + 1, u + 1} where
  Sen := Sentence.{u}
  Mod := Cat.of (Discrete SetHierarchy.{u})
  Sat T j := j.down.Valid (Discrete.as T)

/-- The fixed-language institution of extensional cumulative MLTT. -/
def inst : Discrete Unit ⥤ Room.{u + 1, u + 1, u + 1} :=
  Discrete.functor fun _ => room.{u}

/-- MLTT entailment uses all inference rules and arbitrary judgment hypotheses. -/
def logic : LogicalSystem.{0, 0, u + 1, u + 1, u + 1} (Discrete Unit) where
  I := inst.{u}
  Derives _ H j := ECtx.JEqH (ULift.down '' H) j.down.Γ j.down.A j.down.a j.down.b
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

/-- The bundled MLTT institution for institution and Hets APIs. -/
def bundled : Inst.{0, 0, u + 1, u + 1, u + 1} := logic.{u}.toInst

end Institution

namespace SetTheoryInterpretation

/-- A free-variable environment in the ambient set carrier. -/
abbrev Env := String → ZFSet.{u}

/-- A general environmental equality-and-membership constraint.

This language is independent of MLTT syntax. Its fields are semantic predicates
and functions over sets; they are not first-order set-theory formulas.
-/
structure SetSequent : Type (u + 1) where
  premise : SetHierarchy.{u} → Env.{u} → Prop
  carrier : SetHierarchy.{u} → Env.{u} → ZFSet.{u}
  lhs : SetHierarchy.{u} → Env.{u} → ZFSet.{u}
  rhs : SetHierarchy.{u} → Env.{u} → ZFSet.{u}

/-- A set sequent holds under every environment satisfying its premise. -/
def SetSequent.Valid (T : SetHierarchy.{u}) (s : SetSequent.{u}) : Prop :=
  ∀ ρ, s.premise T ρ → s.lhs T ρ = s.rhs T ρ ∧ s.lhs T ρ ∈ s.carrier T ρ

/-- Expand a judgment into its context premise and set-valued interpretations. -/
noncomputable def interpret (j : Institution.Sentence.{u}) : SetSequent.{u} where
  premise T ρ := j.down.Γ.Sat T ρ
  carrier T ρ := j.down.A.denote T ρ Fin.elim0
  lhs T ρ := j.down.a.denote T ρ Fin.elim0
  rhs T ρ := j.down.b.denote T ρ Fin.elim0

/-- The room of general set constraints over universe hierarchies. -/
def room : Room.{u + 1, u + 1, u + 1} where
  Sen := SetSequent.{u}
  Mod := Cat.of (Discrete SetHierarchy.{u})
  Sat T s := s.Valid (Discrete.as T)

/-- The institution of semantic set constraints. -/
def inst : Discrete Unit ⥤ Room.{u + 1, u + 1, u + 1} :=
  Discrete.functor fun _ => room.{u}

/-- Consequence in the target is semantic consequence of set constraints. -/
def logic : LogicalSystem.{0, 0, u + 1, u + 1, u + 1} (Discrete Unit) where
  I := inst.{u}
  Derives _ := room.{u}.Entails
  refl _ := room.{u}.semanticER.refl
  mono _ := room.{u}.semanticER.mono
  trans _ := room.{u}.semanticER.trans
  map_derives := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ σ H s h
    rw [Subsingleton.elim σ (𝟙 _), CategoryTheory.Functor.map_id]
    simpa using h

def bundled : Inst.{0, 0, u + 1, u + 1, u + 1} := logic.{u}.toInst

/-- Interpretation sends judgments forward and leaves hierarchy models unchanged. -/
noncomputable def corridor : Institution.room.{u} ⟶ room.{u} where
  sen := interpret
  mod := 𝟭 _
  sat _ _ := Iff.rfl

/-- The semantic set interpretation as an institution comorphism.

A later syntactic interpretation into ZF/ZFC formulas can refine this interface.
-/
noncomputable def toSetTheory : Inst.CoHom Institution.bundled.{u} bundled.{u} where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => corridor.{u}

end SetTheoryInterpretation

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
