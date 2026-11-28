module

public import Silmaril.Logic.Abstraction.FirstOrder.Defs
public import Silmaril.Logic.Institution.Borrowing
import Silmaril.Proofs.Logic.Abstraction.FirstOrder.Correctness

@[expose] public section

/-!
The first-order profile keeps all abstraction rules over each translated signature and
uses only canonical models, with equality arrows as in the full abstraction institution.
The model map of the UFOL comorphism sends an equality arrow to the induced isomorphism
arrow of UFOL structures. The profile's morphism into abstraction logic maps models to
their underlying abstraction models and takes each abstraction rule back to itself.
-/

namespace Silmaril.Logic.Abstraction.FirstOrder

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Inst (Disc)

variable {S T : UFOL.Signature} {k l : Nat}

/-- A translated object term denotes the embedded UFOL object at every matching assignment. -/
theorem eval_term (M : UFOL.Structure S) (ν : Valuation (M.carrier ⊕ Bool))
    (scope : Fin k → Fin l) (env : Fin l → M.carrier ⊕ Bool) (ρ : Fin k → M.carrier)
    (h : ∀ i, env (scope i) = .inl (ρ i)) (t : UFOL.Term S k) :
    (term scope t).eval (algebra M) ν env = .inl (t.eval M ρ) :=
  Proofs.Logic.Abstraction.FirstOrder.eval_term M ν scope env ρ h t

/-- Truth of translated formulas agrees with UFOL at every object assignment
and for every schematic valuation. -/
theorem holds_formula (M : UFOL.Structure S) (ν : Valuation (M.carrier ⊕ Bool))
    (scope : Fin k → Fin l) (env : Fin l → M.carrier ⊕ Bool) (ρ : Fin k → M.carrier)
    (h : ∀ i, env (scope i) = .inl (ρ i)) (φ : UFOL.Formula S k) :
    classifiesTrue ((formula scope φ).eval (algebra M) ν env) ↔ φ.Holds M ρ :=
  Proofs.Logic.Abstraction.FirstOrder.holds_formula M ν scope env ρ h φ

/-- A canonical model satisfies a translated rule exactly when its UFOL structure
satisfies the original sentence. -/
theorem sat_sentence (M : UFOL.Structure S) (φ : UFOL.Sentence S) :
    (model M).Sat (sentence φ) ↔ UFOL.Sentence.Holds M φ :=
  Proofs.Logic.Abstraction.FirstOrder.sat_sentence M φ

theorem term_map (f : S ⟶ T) (scope : Fin k → Fin l) (t : UFOL.Term S k) :
    term scope (t.map f) = (term scope t).map (signatureFunctor.map f) :=
  Proofs.Logic.Abstraction.FirstOrder.term_map f scope t

theorem formula_map (f : S ⟶ T) (scope : Fin k → Fin l) (φ : UFOL.Formula S k) :
    formula scope (φ.map f) = (formula scope φ).map (signatureFunctor.map f) :=
  Proofs.Logic.Abstraction.FirstOrder.formula_map f scope φ

theorem sentence_map (f : S ⟶ T) (φ : UFOL.Sentence S) :
    sentence (φ.map f) = (sentence φ).map (signatureFunctor.map f) :=
  congrArg Rule.formula (formula_map f id φ)

/-- Taking the canonical model commutes with reducts, including the valuation space. -/
theorem model_reduct (f : S ⟶ T) (M : UFOL.Structure T) :
    (model M).reduct (signatureFunctor.map f) = model ((UFOL.Structure.reduct f).obj M) :=
  Proofs.Logic.Abstraction.FirstOrder.model_reduct f M

/-- The canonical first-order profile of Abstraction Logic. The underlying UFOL structure
indexes the canonical model, and satisfaction uses the full abstraction rule semantics. -/
noncomputable def profile : Silmaril.Inst.Plain UFOL.Signature where
  Sen S := Sentence (signature S)
  map f := Rule.map (signatureFunctor.map f)
  map_id S r := by rw [signatureFunctor.map_id]; exact r.map_id
  map_comp f g r := by rw [signatureFunctor.map_comp]; exact r.map_comp _ _
  Mod := UFOL.Structure
  reduct f := (UFOL.Structure.reduct f).obj
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M r := (model M).Sat r
  sat_map f M r := ((model M).satisfaction (signatureFunctor.map f) r).trans
    (Iff.of_eq (congrArg (fun N => N.Sat r) (model_reduct f M)))

/-- The canonical first-order profile as a bundled institution. -/
noncomputable def profileInst : Inst.{1, 0, 0, 0, 1} := profile.toInst

/-- Compose the model functor with a UFOL reduct, or first take the profile reduct. -/
theorem toUFOLModels_natural (f : S ⟶ T) :
    toUFOLModels T ⋙ UFOL.Structure.reduct f =
      Disc.functor (UFOL.Structure.reduct f).obj ⋙ toUFOLModels S :=
  Proofs.Logic.Abstraction.FirstOrder.toUFOLModels_natural f

/-- UFOL has a comorphism into the canonical first-order profile. -/
noncomputable def fromUFOL : Inst.CoHom UFOL.inst profileInst where
  Φ := 𝟭 _
  ρ :=
    { app := fun S => ⟨sentence, toUFOLModels S, sat_sentence⟩
      naturality := fun _ _ f =>
        Room.hom_ext (funext (sentence_map f)) (toUFOLModels_natural f) }

/-- The profile has a morphism to full Abstraction Logic. The room corridor acts by the
identity on abstraction rules and sends each profile model to its canonical model. -/
noncomputable def toAbstraction : Inst.Hom profileInst Abstraction.inst where
  Φ := signatureFunctor
  η :=
    { app := fun _ => ⟨id, Disc.functor model, fun _ _ => Iff.rfl⟩
      naturality := fun _ _ f => Room.hom_ext rfl (Silmaril.Inst.Disc.functor_ext (model_reduct f)) }

/-- Every UFOL structure occurs as the reduct of a canonical profile model. -/
theorem fromUFOL_modelExpansive : fromUFOL.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- UFOL consequence is exactly consequence of the translations in the canonical profile. -/
theorem entails_iff (S : UFOL.Signature) (Γ : Set (UFOL.Sentence S)) (φ : UFOL.Sentence S) :
    (UFOL.institution.obj S).Entails Γ φ ↔
      (profileInst.I.obj S).Entails (sentence '' Γ) (sentence φ) :=
  fromUFOL.entails_iff fromUFOL_modelExpansive S Γ φ

/-- Consequence over all abstraction models implies UFOL consequence, since the canonical
models are among them. -/
theorem entails_of_abstraction (S : UFOL.Signature) (Γ : Set (UFOL.Sentence S))
    (φ : UFOL.Sentence S)
    (h : (Abstraction.room (signature S)).Entails (sentence '' Γ) (sentence φ)) :
    (UFOL.institution.obj S).Entails Γ φ :=
  (entails_iff S Γ φ).mpr (fun M hM => h (model M) hM)

end Silmaril.Logic.Abstraction.FirstOrder
