module

public import Silmaril.Logic.Kore.FirstOrder.Thms
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
namespace Silmaril.Logic.Kore.FirstOrder
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)

/-- The named KORE first-order pattern fragment, with its direct satisfaction.
Signatures consist of already instantiated sorted symbol schemas. Model arrows
preserve operation graphs, as in the target matching institution. -/
def institution (S : Type) : Signature S ⥤ Room where
  obj A := ⟨Sentence A, Cat.of (Matching.FirstOrder.Model A), Sentence.Satisfies⟩
  map f := ⟨Sentence.map f, Matching.FirstOrder.SignatureMap.reductFunctor f,
    Sentence.satisfaction f⟩
  map_id _ := by
    apply Room.hom_ext
    · funext p; exact Sentence.map_id p
    · exact Matching.FirstOrder.SignatureMap.reductFunctor_id
  map_comp f g := by
    apply Room.hom_ext
    · funext p; exact Sentence.map_comp f g p
    · exact Matching.FirstOrder.SignatureMap.reductFunctor_comp f g

def inst (S : Type) : Inst := ⟨Signature S, institution S⟩
def matchingInst (S : Type) : Inst := ⟨Signature S, Matching.FirstOrder.institution S⟩

/-- Lower sentences; the model functor is exactly the identity. -/
def loweringNatural (S : Type) : institution S ⟶ Matching.FirstOrder.institution S where
  app A :=
    { sen := Sentence.lower
      mod := 𝟭 (Matching.FirstOrder.Model A)
      sat := Sentence.satisfies_lower }
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p; exact Sentence.lower_map f p
    · rfl

/-- The actual fragment-to-matching comorphism: identity signatures and models,
with explicit primitive expansion on sentences. -/
def loweringComorphism (S : Type) : Inst.CoHom (inst S) (matchingInst S) where
  Φ := 𝟭 _
  ρ := loweringNatural S ≫ (Functor.leftUnitor (Matching.FirstOrder.institution S)).inv

theorem lowering_modelExpansive (S : Type) : (loweringComorphism S).ModelExpansive := by
  intro A M
  exact ⟨M, rfl⟩

abbrev Presentation (S : Type) := Silmaril.Logic.Institution.Presentation (institution S)
abbrev Theory (S : Type) := Silmaril.Logic.Institution.Theory (institution S)
end Silmaril.Logic.Kore.FirstOrder
