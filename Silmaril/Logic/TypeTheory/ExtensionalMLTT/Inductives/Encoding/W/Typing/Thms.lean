module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Typing.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WTyping

@[expose] public section

/-! Actual bounded derivations for generic indexed source telescopes and their raw W carrier. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

def FormationData.weaken {Δ : Ctx} (D : FormationData S levels n Γ) (e : Γ.LookupLE Δ)
    (hΔ : Δ.JEqB levels ∅ .unit .star .star) : FormationData S levels n Δ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.weakenData D e hΔ

theorem totalShape_formation (D : FormationData S levels n Γ H) :
    Γ.JEqB levels H (.univ n) S.totalShape S.totalShape :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.totalShape_formation D

theorem positionFamily_typing (D : FormationData S levels n Γ H) :
    Γ.JEqB levels H (S.positionFamilyType n) S.positionFamily S.positionFamily :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positionFamily_typing D

theorem positionValue_formation (D : FormationData S levels n Γ H) {l : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) :
    Γ.JEqB levels H (.univ n)
      (.app (.app S.positionFamily (.fst l)) (.snd l))
      (.app (.app S.positionFamily (.fst l)) (.snd l)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positionValue_formation D hl

theorem compiledPositions_formation (D : FormationData S levels n Γ) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels ∅ (.univ n)
      (S.compiledPositions.open x) (S.compiledPositions.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledPositions_formation D

/-- The extra universe is the explicit budget of this beta-based construction. -/
theorem compiledRaw_formation (D : FormationData S levels n Γ) :
    Γ.JEqB levels ∅ (.univ n) S.compiledRaw S.compiledRaw :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledRaw_formation D

theorem compiledNode_typing (D : FormationData S levels n Γ) {a f : Tm 0}
    (ha : Γ.JEqB levels ∅ S.totalShape a a)
    (hf : Γ.JEqB levels ∅ (.arr (S.compiledPositions.lst a) S.compiledRaw) f f) :
    Γ.JEqB levels ∅ S.compiledRaw
      (.sup S.totalShape S.compiledPositions a f) (.sup S.totalShape S.compiledPositions a f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledNode_typing D ha hf

theorem compiledRoot_typing_of_hypotheses (hh : HypothesisTransport levels H H) (D : FormationData S levels n Γ H) {t : Tm 0}
    (ht : Γ.JEqB levels H S.compiledRaw t t) :
    Γ.JEqB levels H S.index (S.compiledRoot t) (S.compiledRoot t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledRoot_typing_of_hypotheses hh D ht

theorem compiledRoot_typing (D : FormationData S levels n Γ) {t : Tm 0}
    (ht : Γ.JEqB levels ∅ S.compiledRaw t t) :
    Γ.JEqB levels ∅ S.index (S.compiledRoot t) (S.compiledRoot t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledRoot_typing D ht

/-- Actual source hypotheses are retained in the formation data. -/
def FormationData.monoTheory {K : Set Jdg} (D : FormationData S levels n Γ H) (h : H ⊆ K) :
    FormationData S levels n Γ K where
  bound := D.bound
  names := D.names
  declared := D.declared
  context := D.context.mono h
  index := D.index.mono h
  shape x hx := (D.shape x hx).mono h
  position x hx y hy := (D.position x hx y hy).mono h

def FormationData.weaken_of_hypotheses {K : Set Jdg} {Δ : Ctx} (D : FormationData S levels n Γ H)
    (hh : HypothesisTransport levels H K) (e : Γ.LookupLE Δ)
    (hΔ : Δ.JEqB levels K .unit .star .star) : FormationData S levels n Δ K :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.weakenData_of_hypotheses D hh e hΔ

theorem compiledPositions_formation_of_hypotheses (D : FormationData S levels n Γ H)
    (hh : HypothesisTransport levels H H) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels H (.univ n)
      (S.compiledPositions.open x) (S.compiledPositions.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledPositions_formation_of_hypotheses D hh

/-- Arbitrary source theory is supported once its actual leaves have context transport. -/
theorem compiledRaw_formation_of_hypotheses (D : FormationData S levels n Γ H)
    (hh : HypothesisTransport levels H H) :
    Γ.JEqB levels H (.univ n) S.compiledRaw S.compiledRaw :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledRaw_formation_of_hypotheses D hh

theorem compiledNode_typing_of_hypotheses (D : FormationData S levels n Γ H)
    (hh : HypothesisTransport levels H H) {a f : Tm 0}
    (ha : Γ.JEqB levels H S.totalShape a a)
    (hf : Γ.JEqB levels H (.arr (S.compiledPositions.lst a) S.compiledRaw) f f) :
    Γ.JEqB levels H S.compiledRaw
      (.sup S.totalShape S.compiledPositions a f) (.sup S.totalShape S.compiledPositions a f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledNode_typing_of_hypotheses D hh ha hf

/-- Context closure gives an explicit larger theory and needs no external transport certificate. -/
theorem compiledRaw_formation_contextClosure (D : FormationData S levels n Γ H) :
    Γ.JEqB levels (ContextClosure H) (.univ n) S.compiledRaw S.compiledRaw :=
  compiledRaw_formation_of_hypotheses (D.monoTheory (ContextClosure.includes H))
    (ContextClosure.self_transport levels H)

def nullaryFormationData : FormationData nullaryDescription 2 0 .nil :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullaryFormationData

theorem nullary_raw_formation : Ctx.JEqB 2 ∅ .nil (.univ 0)
    nullaryDescription.compiledRaw nullaryDescription.compiledRaw :=
  compiledRaw_formation nullaryFormationData

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
