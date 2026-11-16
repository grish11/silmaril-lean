module

public import Silmaril.Logic.Separation.Parameterized.Matching.Institution.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.Matching
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
variable {A B : Signature}

/-- Compile arbitrary native positive FO(LFP) pairs into native matching pairs. -/
def realize {S : FOL.Signature} (p : FirstOrder.Canonical.FormulaPair S) :
    Canonical.Native.Pair S :=
  ⟨p.contextSize,p.profiles,p.context,GuardedLFP.formula p.pre,GuardedLFP.formula p.post⟩

theorem realize_satisfaction {S : FOL.Signature} (M : FirstOrderLFP.Model S)
    (p : FirstOrder.Canonical.FormulaPair S) :
    (realize p).Satisfies M ↔ p.Satisfies M := by
  constructor
  · intro h θ hp
    exact (GuardedLFP.expanded_formula_denote M p.post θ ()).mp
      (h θ () ((GuardedLFP.expanded_formula_denote M p.pre θ ()).mpr hp))
  · intro h θ w hp
    exact (GuardedLFP.expanded_formula_denote M p.post θ w).mpr
      (h ((GuardedLFP.expanded_formula_denote M p.pre θ w).mp hp))

theorem realize_map {S T : FOL.Signature} (f : S ⟶ T)
    (p : FirstOrder.Canonical.FormulaPair S) :
    Canonical.Native.Pair.map f (realize p) = realize (p.map f) := by
  cases p with
  | mk k P Γ pre post =>
    exact congrArg₂ (fun a b => (⟨k,fun i => (P i).map f,f.sorts ∘ Γ,a,b⟩ : Canonical.Native.Pair T))
      (GuardedLFP.formula_map f pre) (GuardedLFP.formula_map f post)

def comparison : FirstOrder.Canonical.institution ⟶ (𝟭 Signature) ⋙ Canonical.institution where
  app A := ⟨realize,𝟭 (Model A),fun M p => realize_satisfaction (FirstOrder.model M) p⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p
      exact (realize_map (FirstOrder.signatureMap f) p).symm
    · rfl

def toCanonical : Inst.CoHom FirstOrder.Canonical.inst Canonical.inst := ⟨𝟭 _,comparison⟩

theorem toCanonical_modelExpansive : toCanonical.ModelExpansive := fun _ M => ⟨M,rfl⟩

def sentence (p : Parameterized.Sentence A) : Canonical.Sentence A := realize (FirstOrder.sentence p)

theorem sentence_satisfaction (M : Model A) (p : Parameterized.Sentence A) :
    Canonical.Sentence.Satisfies M (sentence p) ↔ p.Satisfies M :=
  (realize_satisfaction (FirstOrder.model M) (FirstOrder.sentence p)).trans
    (FirstOrder.sentence_satisfaction M p)

theorem sentence_map (f : A ⟶ B) (p : Parameterized.Sentence A) :
    Canonical.Sentence.map f (sentence p) = sentence (p.map f) := by
  change Canonical.Native.Pair.map (FirstOrder.signatureMap f) (realize (FirstOrder.sentence p)) = _
  rw [realize_map]
  exact congrArg realize (FirstOrder.sentence_map f p)

def sourceComparison : Parameterized.institution ⟶ (𝟭 Signature) ⋙ Canonical.institution where
  app A := ⟨sentence,𝟭 (Model A),sentence_satisfaction⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p
      exact (sentence_map f p).symm
    · rfl

def sourceToCanonical : Inst.CoHom Parameterized.inst Canonical.inst := ⟨𝟭 _,sourceComparison⟩

theorem sourceToCanonical_modelExpansive : sourceToCanonical.ModelExpansive := fun _ M => ⟨M,rfl⟩

theorem sat_iff (p : Parameterized.Sentence A) :
    (∃ M : Model A, p.Satisfies M) ↔ ∃ M : Model A, Canonical.Sentence.Satisfies M (sentence p) := by
  constructor
  · rintro ⟨M,h⟩
    exact ⟨M,(sentence_satisfaction M p).mpr h⟩
  · rintro ⟨M,h⟩
    exact ⟨M,(sentence_satisfaction M p).mp h⟩

theorem unsat_iff (p : Parameterized.Sentence A) :
    (¬ ∃ M : Model A, p.Satisfies M) ↔ ¬ ∃ M : Model A, Canonical.Sentence.Satisfies M (sentence p) :=
  not_congr (sat_iff p)

theorem entails_iff (H : Set (Parameterized.Sentence A)) (p : Parameterized.Sentence A) :
    (Parameterized.institution.obj A).Entails H p ↔
      (Canonical.institution.obj A).Entails (sentence '' H) (sentence p) :=
  sourceToCanonical.entails_iff sourceToCanonical_modelExpansive A H p

end Silmaril.Logic.Separation.Parameterized.Matching
