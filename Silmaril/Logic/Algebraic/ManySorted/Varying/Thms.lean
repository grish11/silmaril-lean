module

public import Silmaril.Logic.Algebraic.ManySorted.Varying.Defs
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.ManySorted.Varying
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- The full public signature: unlike the old bridge its sort map is unrestricted. -/
abbrev publicSignature (A : Signature) : EQ.Signature := ⟨A.sorts, A.algebraic.operations⟩
abbrev privateSignature (A : EQ.Signature) : Signature := ⟨A.S, ⟨A.Op⟩⟩

def toPublicSignatures : Signature ⥤ EQ.Signature where
  obj := publicSignature
  map f := ⟨f.sorts, f.operations⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def toPrivateSignatures : EQ.Signature ⥤ Signature where
  obj := privateSignature
  map f := ⟨f.sorts, f.ops⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem privateSignatures_roundtrip : toPublicSignatures ⋙ toPrivateSignatures = 𝟭 Signature := by
  apply Functor.hext (fun A => by cases A; rfl)
  intro A B f
  cases A; cases B; cases f
  rfl

theorem publicSignatures_roundtrip : toPrivateSignatures ⋙ toPublicSignatures = 𝟭 EQ.Signature := by
  apply Functor.hext (fun A => by cases A; rfl)
  intro A B f
  cases A; cases B; cases f
  rfl

variable {A B : Signature}

/-- Existing structural translations, now on every bundled private signature. -/
abbrev toEquation (e : EQ.Equation (publicSignature A)) : Equation A := PublicEQ.toEquation e
abbrev fromEquation (e : Equation A) : EQ.Equation (publicSignature A) := PublicEQ.fromEquation e
abbrev toModel (M : EQ.Algebra (publicSignature A)) : Model A := PublicEQ.toModel M
abbrev fromModel (M : Model A) : EQ.Algebra (publicSignature A) := PublicEQ.fromModel M
abbrev toModels (A : Signature) := PublicEQ.toModels A.algebraic
abbrev fromModels (A : Signature) := PublicEQ.fromModels A.algebraic

theorem to_fromEquation (e : Equation A) : toEquation (fromEquation e) = e :=
  PublicEQ.to_fromEquation e

theorem from_toEquation (e : EQ.Equation (publicSignature A)) : fromEquation (toEquation e) = e :=
  PublicEQ.from_toEquation e

theorem toEquation_map (f : A ⟶ B) (e : EQ.Equation (publicSignature A)) :
    toEquation (e.map (toPublicSignatures.map f)) = mapEquation f (toEquation e) := by
  have terms {k} {Γ : Fin k → A.sorts} {s} (t : EQ.Term (publicSignature A) Γ s) :
      PublicEQ.toTerm (t.map (toPublicSignatures.map f)) =
        mapTerm f (PublicEQ.toTerm t) := by
    exact EQ.Term.rec (motive := fun _ t =>
      PublicEQ.toTerm (t.map (toPublicSignatures.map f)) = mapTerm f (PublicEQ.toTerm t))
      (fun _ => rfl) (fun op _ ih => by
        simp only [EQ.Term.map, PublicEQ.toTerm, mapTerm]
        exact congrArg (ManySorted.Term.app (f.operations op)) (funext ih)) t
  cases e
  simp only [toEquation, PublicEQ.toEquation, EQ.Equation.map, mapEquation, terms]
  rfl

theorem fromEquation_map (f : A ⟶ B) (e : Equation A) :
    fromEquation (mapEquation f e) = (fromEquation e).map (toPublicSignatures.map f) := by
  apply Function.LeftInverse.injective (fun e => from_toEquation e)
  rw [to_fromEquation, toEquation_map, to_fromEquation]

theorem fromModels_reduct (f : A ⟶ B) :
    fromModels B ⋙ EQ.Algebra.reduct (toPublicSignatures.map f) =
      reductFunctor f ⋙ fromModels A := rfl

theorem toModels_reduct (f : A ⟶ B) :
    toModels B ⋙ reductFunctor f =
      EQ.Algebra.reduct (toPublicSignatures.map f) ⋙ toModels A := rfl

def toPublicNatural : institution ⟶ toPublicSignatures ⋙ EQ.institution where
  app A := ⟨fromEquation, toModels A, PublicEQ.reverse_satisfaction⟩
  naturality := by
    intro A B f
    exact Room.hom_ext (funext (fromEquation_map f)) (toModels_reduct f)

/-- Full varying-sort correspondence, reducing actual public algebras backward. -/
def toPublicEQ : Inst.CoHom inst EQ.inst := ⟨toPublicSignatures, toPublicNatural⟩

def toPrivateNatural : EQ.institution ⟶ toPrivateSignatures ⋙ institution where
  app A := ⟨toEquation (A := privateSignature A), fromModels (privateSignature A),
    PublicEQ.satisfaction⟩
  naturality := by
    intro A B f
    exact Room.hom_ext (funext (toEquation_map (toPrivateSignatures.map f)))
      (fromModels_reduct (toPrivateSignatures.map f))

/-- Its reverse starts at the full public EQ institution, without restricting sort maps. -/
def toManySorted : Inst.CoHom EQ.inst inst := ⟨toPrivateSignatures, toPrivateNatural⟩

/-- The round trip is identity on whole private rooms, including model arrows. -/
theorem privateRoom_roundtrip (A : Signature) :
    toPublicNatural.app A ≫ toPrivateNatural.app (publicSignature A) = 𝟙 (room A) := by
  exact Room.hom_ext (funext (to_fromEquation (A := A))) PublicEQ.models_roundtrip

/-- The reverse round trip also retains every public algebra homomorphism. -/
theorem publicRoom_roundtrip (A : EQ.Signature) :
    toPrivateNatural.app A ≫ toPublicNatural.app (privateSignature A) = 𝟙 (EQ.room A) := by
  exact Room.hom_ext (funext (from_toEquation (A := privateSignature A)))
    (PublicEQ.publicModels_roundtrip (A := (privateSignature A).algebraic))

theorem toPublicEQ_modelExpansive : toPublicEQ.ModelExpansive :=
  fun _ M => ⟨fromModel M, PublicEQ.to_fromModel M⟩

theorem toManySorted_modelExpansive : toManySorted.ModelExpansive :=
  fun A M => ⟨toModel (A := privateSignature A) M,
    PublicEQ.from_toModel (A := (privateSignature A).algebraic) M⟩

/-- This expansion concerns the conversion comorphism, not arbitrary signature maps. -/
theorem entails_iff (A : Signature) (H : Set (Equation A)) (e : Equation A) :
    (room A).Entails H e ↔
      (EQ.room (publicSignature A)).Entails (fromEquation '' H) (fromEquation e) :=
  toPublicEQ.entails_iff toPublicEQ_modelExpansive A H e

theorem sat_iff (A : Signature) (H : Set (Equation A)) :
    (∃ M : Model A, ∀ e ∈ H, ManySorted.Equation.Satisfies M e) ↔
      ∃ M : EQ.Algebra (publicSignature A), ∀ e ∈ H, (fromEquation e).Holds M := by
  constructor
  · rintro ⟨M, h⟩
    exact ⟨fromModel M, fun e he =>
      (PublicEQ.reverse_satisfaction (fromModel M) e).mpr
        (by simpa only [PublicEQ.to_fromModel] using h e he)⟩
  · rintro ⟨M, h⟩
    exact ⟨toModel M, fun e he => (PublicEQ.reverse_satisfaction M e).mp (h e he)⟩

theorem unsat_iff (A : Signature) (H : Set (Equation A)) :
    (¬ ∃ M : Model A, ∀ e ∈ H, ManySorted.Equation.Satisfies M e) ↔
      ¬ ∃ M : EQ.Algebra (publicSignature A), ∀ e ∈ H, (fromEquation e).Holds M :=
  not_congr (sat_iff A H)

/-- The public endpoint is the full institution, not its fixed-sort restriction. -/
theorem public_entails_iff (A : EQ.Signature) (H : Set (EQ.Equation A)) (e : EQ.Equation A) :
    (EQ.room A).Entails H e ↔
      (room (privateSignature A)).Entails (toEquation '' H) (toEquation e) :=
  toManySorted.entails_iff toManySorted_modelExpansive A H e

theorem public_sat_iff (A : EQ.Signature) (H : Set (EQ.Equation A)) :
    (∃ M : EQ.Algebra A, ∀ e ∈ H, e.Holds M) ↔
      ∃ M : Model (privateSignature A), ∀ e ∈ H,
        ManySorted.Equation.Satisfies M (toEquation (A := privateSignature A) e) := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨toModel (A := privateSignature A) M, fun e he => ?_⟩
    apply (PublicEQ.satisfaction (toModel (A := privateSignature A) M) e).mpr
    rw [PublicEQ.from_toModel]
    exact h e he
  · rintro ⟨M, h⟩
    exact ⟨fromModel M, fun e he => (PublicEQ.satisfaction M e).mp (h e he)⟩

theorem public_unsat_iff (A : EQ.Signature) (H : Set (EQ.Equation A)) :
    (¬ ∃ M : EQ.Algebra A, ∀ e ∈ H, e.Holds M) ↔
      ¬ ∃ M : Model (privateSignature A), ∀ e ∈ H,
        ManySorted.Equation.Satisfies M (toEquation (A := privateSignature A) e) :=
  not_congr (public_sat_iff A H)

end Silmaril.Logic.Algebraic.ManySorted.Varying
