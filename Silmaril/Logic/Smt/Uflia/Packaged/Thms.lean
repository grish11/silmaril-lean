module

public import Silmaril.Logic.Smt.Uflia.Packaged.Defs
import Silmaril.Proofs.Logic.Smt.Uflia.PackagedDeclarationNames

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.Packaged

open CategoryTheory Silmaril.Inst
open Silmaril.Logic.Institution
open SExpr

/-- A finite, syntactic uniqueness condition suffices for model expansion.
It is stronger than per-profile uniqueness and mentions no semantic result. -/
theorem namesInjective_of_declarationNames (E : Environment)
    (h : Function.Injective (fun i : Fin E.declarations.length =>
      (E.declarations.get i).name)) : NamesInjective E :=
  Silmaril.Proofs.Logic.Smt.Uflia.PackagedDeclarationNames.namesInjective_of_declarationNames E h

/-- Successful decoding enforces globally unique declaration names. -/
theorem checked_declarationNames_nodup (checked : DeclarationPrefix) :
    (checked.environment.declarations.map Declaration.name).Nodup :=
  Silmaril.Proofs.Logic.Smt.Uflia.PackagedDeclarationNames.checked_declarationNames_nodup checked

/-- The checked declaration prefix supplies the required structural hypothesis;
no solver answer or model property is assumed. -/
theorem checked_namesInjective (checked : DeclarationPrefix) :
    NamesInjective checked.environment :=
  Silmaril.Proofs.Logic.Smt.Uflia.PackagedDeclarationNames.checked_namesInjective checked

theorem holds_iff (E : Environment) (Γ : Problem E.signature) (M : GlobalModel) :
    (Sentence.mk E Γ).Holds M ↔ Γ.Holds (M.reduct (nameMap E)) := by
  constructor
  · intro h φ hφ
    exact (M.holds_map (nameMap E) φ).mp (h φ hφ)
  · intro h φ hφ
    exact (M.holds_map (nameMap E) φ).mpr (h φ hφ)

/-- Fixed symbols move into each sentence's environment, while global models
reduce by their interpretations of those declaration names. -/
noncomputable def packagingCorridor (E : Environment) : fixedRoom E ⟶ wholeRoom where
  sen Γ := ⟨E, Γ⟩
  mod := Disc.functor (fun M : GlobalModel => M.reduct (nameMap E))
  sat M Γ := holds_iff E Γ M

/-- Packaging is natural across all equality transports of raw environments,
giving an actual institution comorphism to the whole-problem presentation. -/
noncomputable def packagingComorphism : Comorphism rawInstitution institution :=
  Comorphism.ofPlain (Disc.functor (fun _ : Environment => ()))
    (fun E Γ => ⟨E, Γ⟩) (fun E M => M.reduct (nameMap E))
    (fun E M Γ => holds_iff E Γ M)
    (by
      intro E E' σ Γ
      rcases σ with ⟨h⟩
      cases h
      rfl)
    (by
      intro E E' σ M
      rcases σ with ⟨h⟩
      cases h
      rfl)

/-- The checked-prefix restriction has the same packaging semantics. -/
noncomputable def checkedPackagingComorphism : Comorphism checkedInstitution institution :=
  Comorphism.ofPlain (Disc.functor (fun _ : DeclarationPrefix => ()))
    (fun checked Γ => ⟨checked.environment, Γ⟩)
    (fun checked M => M.reduct (nameMap checked.environment))
    (fun checked M Γ => holds_iff checked.environment Γ M)
    (by
      intro checked checked' σ Γ
      rcases σ with ⟨h⟩
      cases h
      rfl)
    (by
      intro checked checked' σ M
      rcases σ with ⟨h⟩
      cases h
      rfl)

theorem expand_reduct (E : Environment) (hE : NamesInjective E)
    (M : Model E.signature) : (expand E M).reduct (nameMap E) = M := by
  classical
  cases M with
  | mk carriers operation =>
    unfold Model.reduct expand
    congr 1
    funext n inputs output symbol args
    change (if h : ∃ s : E.signature.operations n inputs output,
        (nameMap E).operations s = (nameMap E).operations symbol then
      operation (Classical.choose h) args else defaultValue carriers output) =
      operation symbol args
    have hex : ∃ s : E.signature.operations n inputs output,
        (nameMap E).operations s = (nameMap E).operations symbol := ⟨symbol, rfl⟩
    rw [dite_eq_left hex]
    rw [hE n inputs output (Classical.choose_spec hex)]

theorem packaging_modelExpansive (E : Environment) (hE : NamesInjective E) :
    (packagingCorridor E).ModelExpansive := by
  intro M
  exact ⟨expand E M, expand_reduct E hE M⟩

/-- A coherent whole model always restricts to a fixed-signature witness. -/
theorem fixed_sat_of_whole_sat (E : Environment) (Γ : Problem E.signature)
    (h : (Sentence.mk E Γ).Sat) : Γ.Sat := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M.reduct (nameMap E), (holds_iff E Γ M).mp hM⟩

theorem whole_sat_of_fixed_sat (E : Environment) (hE : NamesInjective E)
    (Γ : Problem E.signature) (h : Γ.Sat) : (Sentence.mk E Γ).Sat := by
  obtain ⟨M, hM⟩ := h
  refine ⟨expand E M, (holds_iff E Γ (expand E M)).mpr ?_⟩
  rw [expand_reduct E hE M]
  exact hM

theorem sat_iff (E : Environment) (hE : NamesInjective E) (Γ : Problem E.signature) :
    (Sentence.mk E Γ).Sat ↔ Γ.Sat :=
  ⟨fixed_sat_of_whole_sat E Γ, whole_sat_of_fixed_sat E hE Γ⟩

theorem whole_unsat_of_fixed_unsat (E : Environment) (Γ : Problem E.signature)
    (h : Γ.Unsat) : (Sentence.mk E Γ).Unsat :=
  fun hsat => h (fixed_sat_of_whole_sat E Γ hsat)

theorem unsat_iff (E : Environment) (hE : NamesInjective E) (Γ : Problem E.signature) :
    (Sentence.mk E Γ).Unsat ↔ Γ.Unsat := not_congr (sat_iff E hE Γ)

theorem checked_packaging_modelExpansive (checked : DeclarationPrefix) :
    (packagingCorridor checked.environment).ModelExpansive :=
  packaging_modelExpansive checked.environment (checked_namesInjective checked)

/-- Every fixed-signature model at every checked prefix expands to one global
typed-name model. This supports institution-level consequence borrowing. -/
theorem checkedPackagingComorphism_modelExpansive :
    ∀ S, Silmaril.Logic.Institution.Corridor.ModelExpansive (checkedPackagingComorphism.ρ.app S) := by
  intro checked M
  exact ⟨expand checked.environment M,
    expand_reduct checked.environment (checked_namesInjective checked) M⟩

theorem checked_sat_iff (checked : DeclarationPrefix)
    (Γ : Problem checked.environment.signature) :
    (Sentence.mk checked.environment Γ).Sat ↔ Γ.Sat :=
  sat_iff checked.environment (checked_namesInjective checked) Γ

theorem checked_unsat_iff (checked : DeclarationPrefix)
    (Γ : Problem checked.environment.signature) :
    (Sentence.mk checked.environment Γ).Unsat ↔ Γ.Unsat :=
  unsat_iff checked.environment (checked_namesInjective checked) Γ

/-- Concrete decoding and fixed-to-whole packaging agree in the same global model. -/
theorem concrete_holds_iff (s : ConcreteSentence) (M : GlobalModel) :
    s.Holds M ↔ s.toAbstract.Holds M :=
  (assertionsHolds_iff s.assertions (M.reduct (nameMap s.checked.environment))).trans
    (holds_iff s.checked.environment (s.assertions.map Assertion.formula) M).symm

/-- Typed decoding for fixed concrete assertion lists. -/
noncomputable def concreteFixedDecodeComorphism :
    Comorphism concreteFixedInstitution checkedInstitution :=
  Comorphism.ofPlain (𝟭 _) (fun _ Γ => Γ.map Assertion.formula) (fun _ => id)
    (fun _ M Γ => (assertionsHolds_iff Γ M).symm)
    (by
      intro checked checked' σ Γ
      rcases σ with ⟨h⟩
      cases h
      rfl)
    (by
      intro checked checked' σ M
      rcases σ with ⟨h⟩
      cases h
      rfl)

theorem concreteFixedDecodeComorphism_modelExpansive :
    ∀ S, Silmaril.Logic.Institution.Corridor.ModelExpansive (concreteFixedDecodeComorphism.ρ.app S) := fun _ M => ⟨M, rfl⟩

/-- Move the checked declaration prefix into each concrete problem sentence. -/
noncomputable def concretePackagingComorphism :
    Comorphism concreteFixedInstitution concreteInstitution :=
  Comorphism.ofPlain (Disc.functor (fun _ : DeclarationPrefix => ()))
    (fun checked Γ => ConcreteSentence.mk checked Γ)
    (fun checked M => M.reduct (nameMap checked.environment))
    (fun _ _ _ => Iff.rfl)
    (by
      intro checked checked' σ Γ
      rcases σ with ⟨h⟩
      cases h
      rfl)
    (by
      intro checked checked' σ M
      rcases σ with ⟨h⟩
      cases h
      rfl)

theorem concretePackagingComorphism_modelExpansive :
    ∀ S, Silmaril.Logic.Institution.Corridor.ModelExpansive (concretePackagingComorphism.ρ.app S) := by
  intro checked M
  exact ⟨expand checked.environment M,
    expand_reduct checked.environment (checked_namesInjective checked) M⟩

/-- Actual whole-problem concrete-to-abstract institution map. It leaves
global models unchanged and uses the checked assertion decoder on sentences. -/
noncomputable def concreteDecodeComorphism :
    Comorphism concreteInstitution institution :=
  Comorphism.ofPlain (𝟭 _) (fun _ => ConcreteSentence.toAbstract) (fun _ => id)
    (fun _ M s => (concrete_holds_iff s M).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem concreteDecodeComorphism_modelExpansive :
    ∀ S, Silmaril.Logic.Institution.Corridor.ModelExpansive (concreteDecodeComorphism.ρ.app S) := fun _ M => ⟨M, rfl⟩

/-- The concrete/abstract and fixed/whole square commutes as actual institution
comorphisms, including signature functors and sentence/model naturality. -/
theorem packaging_decode_square :
    Inst.CoHom.comp concreteFixedDecodeComorphism checkedPackagingComorphism =
      Inst.CoHom.comp concretePackagingComorphism concreteDecodeComorphism := by
  apply Inst.CoHom.ext rfl
  simp only [eqToHom_refl, Category.comp_id]

/-- The room-level decoder is the component of the genuine comorphism. -/
noncomputable def concreteDecodeCorridor : concreteRoom ⟶ wholeRoom :=
  concreteDecodeComorphism.ρ.app ()

theorem concrete_sat_iff (s : ConcreteSentence) : s.Sat ↔ s.toAbstract.Sat := by
  constructor
  · rintro ⟨M, h⟩
    exact ⟨M, (concrete_holds_iff s M).mp h⟩
  · rintro ⟨M, h⟩
    exact ⟨M, (concrete_holds_iff s M).mpr h⟩

theorem concrete_unsat_iff (s : ConcreteSentence) : s.Unsat ↔ s.toAbstract.Unsat :=
  not_congr (concrete_sat_iff s)

/-- Accepted concrete whole problems and their finite fixed-symbol assertion
lists have exactly the same satisfiability, with no extra uniqueness premise. -/
theorem concrete_sat_iff_fixed (s : ConcreteSentence) :
    s.Sat ↔ Problem.Sat (s.assertions.map Assertion.formula) :=
  (concrete_sat_iff s).trans (checked_sat_iff s.checked _)

theorem concrete_unsat_iff_fixed (s : ConcreteSentence) :
    s.Unsat ↔ Problem.Unsat (s.assertions.map Assertion.formula) :=
  not_congr (concrete_sat_iff_fixed s)

end Silmaril.Logic.Smt.Uflia.Packaged
