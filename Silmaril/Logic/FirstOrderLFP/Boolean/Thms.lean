module

public import Silmaril.Proofs.Logic.FirstOrderLFP.Boolean.Renaming

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP.Boolean
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

/-- Closed Boolean formulas have no free predicates or object variables. -/
structure Sentence (S : Signature) where
  profiles : Fin 0 → Profile S
  context : Fin 0 → S.S
  formula : Formula S profiles context (fun _ => true)

def Sentence.map {S T : Signature} (f : S ⟶ T) (p : Sentence S) : Sentence T :=
  ⟨fun i => (p.profiles i).map f, f.sorts ∘ p.context, p.formula.map f⟩

def Sat {S : Signature} (M : Model S) (p : Sentence S) : Prop :=
  (fun i => i.elim0) ∈ p.formula.denote M (fun i => i.elim0)

theorem Sentence.map_id {S : Signature} (p : Sentence S) : p.map (𝟙 S) = p := by
  obtain ⟨P, Γ, p⟩ := p
  exact congrArg (Sentence.mk P Γ) p.map_id

theorem Sentence.map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
    (p : Sentence S) : p.map (f ≫ g) = (p.map f).map g := by
  obtain ⟨P, Γ, p⟩ := p
  exact congrArg (Sentence.mk _ _) (p.map_comp f g)

theorem sat_map {S T : Signature} (f : S ⟶ T) (M : Model T) (p : Sentence S) :
    Sat M (p.map f) ↔ Sat ((reduct f).obj M) p := by
  unfold Sat Sentence.map
  rw [Formula.denote_map]
  rfl

def institution : Signature ⥤ Room.{0, 0, 1} where
  obj S := ⟨Sentence S, Cat.of (Model S), Sat⟩
  map f := ⟨Sentence.map f, reduct f, sat_map f⟩
  map_id _ := Room.hom_ext (funext Sentence.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) rfl

/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst := (⟨Signature, institution⟩ : Silmaril.Logic.Institution.Inst)

def positiveSentence {S : Signature} (p : FirstOrderLFP.Sentence S) : Sentence S :=
  ⟨p.profiles, p.context, positive p.formula⟩

theorem positiveSentence_sat {S : Signature} (M : Model S) (p : FirstOrderLFP.Sentence S) :
    Sat M (positiveSentence p) ↔ FirstOrderLFP.Sat M p := by
  unfold Sat positiveSentence FirstOrderLFP.Sat
  rw [positive_denote]

/-- The original positive institution is included with exactly the same actual
model objects, equality arrows and contravariant signature reducts. -/
def positiveNatural : FirstOrderLFP.institution ⟶ (𝟭 Signature) ⋙ institution where
  app S := ⟨positiveSentence, 𝟭 (Model S), positiveSentence_sat⟩
  naturality := by
    intro S T f
    apply Room.hom_ext
    · funext p
      exact congrArg (Sentence.mk _ _) (positiveWith_map f p.formula _ _).symm
    · rfl

def fromPositive : Inst.CoHom ⟨Signature, FirstOrderLFP.institution⟩ ⟨Signature, institution⟩ :=
  ⟨𝟭 Signature, positiveNatural⟩

theorem fromPositive_modelExpansive : fromPositive.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

theorem positive_entails_iff (S : Signature) (H : Set (FirstOrderLFP.Sentence S))
    (p : FirstOrderLFP.Sentence S) :
    (FirstOrderLFP.institution.obj S).Entails H p ↔
      (institution.obj S).Entails (positiveSentence '' H) (positiveSentence p) :=
  fromPositive.entails_iff fromPositive_modelExpansive S H p

end Silmaril.Logic.FirstOrderLFP.Boolean
