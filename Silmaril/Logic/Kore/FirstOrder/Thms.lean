module

public import Silmaril.Logic.Kore.FirstOrder.Defs
public import Silmaril.Proofs.Logic.Kore.FirstOrder

@[expose] public section
namespace Silmaril.Logic.Kore.FirstOrder
open CategoryTheory
open Algebraic.ManySorted (Signature)
variable {S : Type} {A B C : Signature S}

/-- Every source constructor has the same denotation after primitive lowering. -/
theorem denote_lower (M : Matching.FirstOrder.Model A) {k : Nat} {Γ : Fin k → S} {s : S}
    (p : Pattern A Γ s) : ∀ v : (i : Fin k) → M.carrier (Γ i),
      M.denote v p.lower = denote A M v p :=
  Silmaril.Proofs.Logic.Kore.FirstOrder.denote_lower M p

namespace Pattern
@[simp] theorem map_id {k : Nat} {Γ : Fin k → S} {s : S} (p : Pattern A Γ s) :
    map (𝟙 A) p = p := Silmaril.Proofs.Logic.Kore.FirstOrder.pattern_map_id p

@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) {k : Nat} {Γ : Fin k → S} {s : S}
    (p : Pattern A Γ s) : map (f ≫ g) p = map g (map f p) :=
  Silmaril.Proofs.Logic.Kore.FirstOrder.pattern_map_comp f g p

/-- Lowering commutes with the actual many-sorted signature maps. -/
theorem lower_map (f : A ⟶ B) {k : Nat} {Γ : Fin k → S} {s : S} (p : Pattern A Γ s) :
    (p.map f).lower = Matching.FirstOrder.Pattern.map f p.lower :=
  Silmaril.Proofs.Logic.Kore.FirstOrder.pattern_lower_map f p
end Pattern

theorem denote_map (f : A ⟶ B) (M : Matching.FirstOrder.Model B) {k : Nat}
    {Γ : Fin k → S} {s : S} (p : Pattern A Γ s) (v : (i : Fin k) → M.carrier (Γ i)) :
    denote B M v (p.map f) = denote A (Matching.FirstOrder.SignatureMap.reduct f M) v p :=
  Silmaril.Proofs.Logic.Kore.FirstOrder.denote_map f M p v

namespace Sentence
theorem satisfies_lower (M : Matching.FirstOrder.Model A) (p : Sentence A) :
    Matching.FirstOrder.Sentence.Satisfies M p.lower ↔ Satisfies M p := by
  simp only [Matching.FirstOrder.Sentence.Satisfies, lower, Satisfies, denote_lower]
  rfl

@[simp] theorem map_id (p : Sentence A) : map (𝟙 A) p = p := by cases p; simp [map]
@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    map (f ≫ g) p = map g (map f p) := by cases p; simp [map]
theorem lower_map (f : A ⟶ B) (p : Sentence A) :
    (map f p).lower = Matching.FirstOrder.Sentence.map f p.lower := by
  cases p; simp only [map, lower, Matching.FirstOrder.Sentence.map, Pattern.lower_map]
theorem satisfaction (f : A ⟶ B) (M : Matching.FirstOrder.Model B) (p : Sentence A) :
    Satisfies M (map f p) ↔ Satisfies (Matching.FirstOrder.SignatureMap.reduct f M) p := by
  simp only [Satisfies, map, denote_map]
  rfl
end Sentence
end Silmaril.Logic.Kore.FirstOrder
