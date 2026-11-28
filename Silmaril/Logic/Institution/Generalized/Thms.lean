module

public import Silmaril.Logic.Institution.Generalized.Defs
import Silmaril.Proofs.Logic.Institution.Generalized.Laws

@[expose] public section

namespace Silmaril.Logic.Institution.Generalized

open CategoryTheory Opposite

universe u v w m₁ m₂ d

variable {Sign : Type u} [Category.{v} Sign] {D : Type d}

namespace ExactInstitution

@[simp] theorem toClassic_ofClassic (J : ClassicInstitution.{u,v,w,m₁,m₂} Sign) :
    (ofClassic J).toClassic = J := by cases J; rfl

@[simp] theorem ofClassic_toClassic (I : ExactInstitution.{u,v,w,m₁,m₂,0} Sign Prop) :
    ofClassic I.toClassic = I := by cases I; rfl

@[simp] theorem atType_toTyped (I : ExactInstitution.{u,v,w,m₁,m₂,d} Sign D) (t : Unit) :
    I.toTyped.atType t = I := by cases I; rfl

@[simp] theorem propInstitution_toTyped_ofClassic (J : ClassicInstitution.{u,v,w,m₁,m₂} Sign) :
    (ofClassic J).toTyped.propInstitution () (Equiv.refl Prop) = J := by cases J; rfl

/-- The induced entailment uses the existing room semantics verbatim. -/
theorem entails_iff_room_entails (I : ExactInstitution.{u,v,w,m₁,m₂,d} Sign D)
    (accepts : D → Prop) {S : Sign} (Γ : Set (I.Sen.obj S)) (φ : I.Sen.obj S) :
    I.toEvaluation.entails accepts Γ φ ↔ ((I.observe accepts).room S).Entails Γ φ :=
  Iff.rfl

end ExactInstitution

namespace LaxInstitution

section Preorder

variable [Preorder D] (I : LaxInstitution.{u,v,w,m₁,m₂,d} Sign D)

/-- The lax comparison for a composite follows by transitivity from its two parts. -/
theorem le_eval_map_comp {S T U : Sign} (σ : S ⟶ T) (τ : T ⟶ U)
    (M : I.Mod.obj (op U)) (φ : I.Sen.obj S) :
    I.eval S ((I.Mod.map (σ ≫ τ).op).toFunctor.obj M) φ ≤
      I.eval U M (I.Sen.map (σ ≫ τ) φ) :=
  Proofs.Logic.Institution.Generalized.le_eval_map_comp I σ τ M φ

/-- Upper cuts transfer from the reduct to the model of the translated sentence. -/
theorem cut_preserved (threshold : D) {S T : Sign} (σ : S ⟶ T)
    (M : I.Mod.obj (op T)) (φ : I.Sen.obj S)
    (h : threshold ≤ I.eval S ((I.Mod.map σ.op).toFunctor.obj M) φ) :
    threshold ≤ I.eval T M (I.Sen.map σ φ) :=
  h.trans (I.le_eval_map σ M φ)

/-- Reflection is necessary and sufficient for the cut's satisfaction equivalence. -/
theorem reflectsCut_iff (threshold : D) :
    I.ReflectsCut threshold ↔
      ∀ {S T : Sign} (σ : S ⟶ T) (M : I.Mod.obj (op T)) (φ : I.Sen.obj S),
        threshold ≤ I.eval T M (I.Sen.map σ φ) ↔
          threshold ≤ I.eval S ((I.Mod.map σ.op).toFunctor.obj M) φ :=
  ⟨fun h {_ _} σ M φ => ⟨h σ M φ, I.cut_preserved threshold σ M φ⟩,
    fun h {_ _} σ M φ => (h σ M φ).mp⟩

end Preorder

/-- In a partial order, reflection at every threshold forces evaluation equality. -/
theorem all_cuts_reflect_iff_exact [PartialOrder D] (J : LaxInstitution.{u,v,w,m₁,m₂,d} Sign D) :
    (∀ threshold, J.ReflectsCut threshold) ↔
      ∀ {S T : Sign} (σ : S ⟶ T) (M : J.Mod.obj (op T)) (φ : J.Sen.obj S),
        J.eval T M (J.Sen.map σ φ) = J.eval S ((J.Mod.map σ.op).toFunctor.obj M) φ :=
  ⟨fun h {_ _} σ M φ => le_antisymm (h _ σ M φ le_rfl) (J.le_eval_map σ M φ),
    fun h _ {_ _} σ M φ ht => (h σ M φ) ▸ ht⟩

end LaxInstitution

namespace Evidence

theorem ofThree_injective : Function.Injective ofThree :=
  Proofs.Logic.Institution.Generalized.ofThree_injective

/-- The three-valued fragment has consistent evidence. -/
theorem ofThree_consistent (value : Option Bool) :
    ¬ ((ofThree value).positive ∧ (ofThree value).negative) := by
  rintro ⟨rfl, h⟩
  cases h

/-- Fewer completions can add either universal flag. -/
theorem ofCompletions_antitone {M : Type*} (holds : M → Prop) :
    Antitone (ofCompletions · holds) :=
  fun _ _ h => ⟨fun ha x hx => ha x (h hx), fun ha x hx => ha x (h hx)⟩

/-- A compatible reduct gives the same flags as evaluation on its image. -/
theorem ofCompletions_image {M N : Type*} (reduct : N → M) (completions : Set N)
    (holds : M → Prop) (holds' : N → Prop)
    (commutes : ∀ n ∈ completions, holds' n ↔ holds (reduct n)) :
    ofCompletions completions holds' = ofCompletions (reduct '' completions) holds :=
  Proofs.Logic.Institution.Generalized.ofCompletions_image reduct completions holds holds' commutes

/-- Coverage means surjectivity onto the specified family of completions. -/
theorem ofCompletions_eq_of_image_eq {M N : Type*} (reduct : N → M) {xs : Set M} {ys : Set N}
    (covers : reduct '' ys = xs) (holds : M → Prop) (holds' : N → Prop)
    (commutes : ∀ n ∈ ys, holds' n ↔ holds (reduct n)) :
    ofCompletions ys holds' = ofCompletions xs holds := by
  rw [ofCompletions_image reduct ys holds holds' commutes, covers]

/-- An empty family has both universal flags by vacuity. -/
theorem ofCompletions_empty {M : Type*} (holds : M → Prop) :
    ofCompletions (∅ : Set M) holds = ⟨True, True⟩ := by
  apply Evidence.ext <;> simp [ofCompletions]

/-- A singleton reports the result and its negation as the two universal flags. -/
theorem ofCompletions_singleton {M : Type*} (x : M) (holds : M → Prop) :
    ofCompletions ({x} : Set M) holds = ⟨holds x, ¬ holds x⟩ := by
  apply Evidence.ext <;> simp [ofCompletions]

/-- A family with a satisfying and a refuting completion has neither universal flag. -/
theorem ofCompletions_mixed {M : Type*} {xs : Set M} {holds : M → Prop}
    {x y : M} (hx : x ∈ xs) (hy : y ∈ xs) (yes : holds x) (no : ¬ holds y) :
    ofCompletions xs holds = ⟨False, False⟩ :=
  Evidence.ext (propext (iff_false_intro fun h => no (h y hy)))
    (propext (iff_false_intro fun h => h x hx yes))

/-- For an inhabited family the two universal flags cannot both hold. -/
theorem ofCompletions_consistent {M : Type*} {xs : Set M} (hne : xs.Nonempty) (holds : M → Prop) :
    ¬ ((ofCompletions xs holds).positive ∧ (ofCompletions xs holds).negative) := by
  obtain ⟨x, hx⟩ := hne
  exact fun ⟨pos, neg⟩ => neg x hx (pos x hx)

end Evidence

namespace Evaluation

/-- The positive theory flag is exactly the observed semantic consequence. -/
theorem entailmentEvidence_positive (E : Evaluation.{u,v,w,m₁,m₂,d} Sign D)
    (accepts : D → Prop) {S : Sign} (Γ : Set (E.Sen.obj S)) (φ : E.Sen.obj S) :
    (E.entailmentEvidence accepts Γ φ).positive ↔ E.entails accepts Γ φ :=
  Iff.rfl

end Evaluation

end Silmaril.Logic.Institution.Generalized
