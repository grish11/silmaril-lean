module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.Institution.Defs
public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface.Thms

/-! Actual accepted source in a checked local declaration environment, interpreted
in a varying ambient signature. Mapping retains the original bytes and changes
only their interpretation; it does not rename or reparse source text. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Source
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

/-- A local signature comes from successfully decoded declaration forms. -/
abbrev localSignature (checked : Uflia.SExpr.DeclarationPrefix) : Signature :=
  ⟨String, checked.environment.signature⟩

/-- The original declaration and expression acceptance receipts remain intact. -/
structure Family (A : Signature) where
  checked : Uflia.SExpr.DeclarationPrefix
  accepted : Quantified.SExpr.ByteAccepted checked.environment
  interpretation : localSignature checked ⟶ A

namespace Family
variable {A B C : Signature}

/-- Independent source evaluation in the actual ambient-model reduct. Typed
sentence evaluation is used only in the separately proved decoder comparison. -/
def Holds (M : Model A.symbols) (s : Family A) : Prop :=
  Quantified.SExpr.Surface.Holds s.checked.environment
    (Hom.reduct s.interpretation M) s.accepted.expression

def map (f : A ⟶ B) (s : Family A) : Family B :=
  ⟨s.checked, s.accepted, s.interpretation ≫ f⟩

@[simp] theorem map_checked (f : A ⟶ B) (s : Family A) :
    (s.map f).checked = s.checked := rfl

@[simp] theorem map_bytes (f : A ⟶ B) (s : Family A) :
    (s.map f).accepted.bytes = s.accepted.bytes := rfl

@[simp] theorem map_id (s : Family A) : s.map (𝟙 A) = s := by
  cases s
  simp only [map, Category.comp_id]

@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (s : Family A) :
    s.map (f ≫ g) = (s.map f).map g := by
  change Family.mk s.checked s.accepted (s.interpretation ≫ (f ≫ g)) =
    Family.mk s.checked s.accepted ((s.interpretation ≫ f) ≫ g)
  rw [Category.assoc]

theorem holds_map (f : A ⟶ B) (M : Model B.symbols) (s : Family A) :
    (s.map f).Holds M ↔ s.Holds (Hom.reduct f M) := by
  unfold Holds map
  rw [Hom.model_reduct_comp]

/-- Decode locally, then transport through the recorded sort and symbol map. -/
def decode (s : Family A) : Quantified.Sentence A.symbols :=
  Hom.quantifiedSentence s.interpretation s.accepted.sentence

theorem decode_holds (M : Model A.symbols) (s : Family A) :
    s.decode.Holds M ↔ s.Holds M :=
  (Hom.holds_quantifiedSentence s.interpretation M s.accepted.sentence).trans
    (Quantified.SExpr.Surface.accepted_holds_iff
      (Hom.reduct s.interpretation M) s.accepted).symm

theorem decode_map (f : A ⟶ B) (s : Family A) :
    (s.map f).decode = Hom.quantifiedSentence f s.decode :=
  Hom.quantifiedSentence_comp s.interpretation f s.accepted.sentence

/-- Package actual accepted local source without changing its interpretation. -/
def ofAccepted (checked : Uflia.SExpr.DeclarationPrefix)
    (accepted : Quantified.SExpr.ByteAccepted checked.environment) :
    Family (localSignature checked) := ⟨checked, accepted, 𝟙 _⟩

theorem ofAccepted_holds (checked : Uflia.SExpr.DeclarationPrefix)
    (accepted : Quantified.SExpr.ByteAccepted checked.environment)
    (M : Model checked.environment.signature) :
    (ofAccepted checked accepted).Holds M ↔
      Quantified.SExpr.Surface.Holds checked.environment M accepted.expression := by
  unfold Holds ofAccepted
  rw [Hom.model_reduct_id]

end Family

/-- All ordinary operation-preserving model homomorphisms are retained. No
truth preservation along arbitrary model homomorphisms is asserted. -/
def room (A : Signature) : Room.{0,0,1} :=
  ⟨Family A, Cat.of (Model A.symbols), Family.Holds⟩

def corridor {A B : Signature} (f : A ⟶ B) : room A ⟶ room B :=
  ⟨Family.map f, Hom.reductFunctor f, Family.holds_map f⟩

def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id A := Room.hom_ext (funext Family.map_id) (Hom.model_reductFunctor_id A)
  map_comp f g := Room.hom_ext (funext (Family.map_comp f g))
    (Hom.model_reductFunctor_comp f g)

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

/-- Exact comparison into full quantified syntax, with identity model functors. -/
def toQuantified : Inst.CoHom inst QuantifiedModels.inst where
  Φ := 𝟭 _
  ρ :=
    { app A := ⟨Family.decode, 𝟭 _, Family.decode_holds⟩
      naturality := by
        intro A B f
        exact Room.hom_ext (funext (Family.decode_map f)) rfl }

/-- A checked fixed-source room uses the same independent interpreter and every
ordinary homomorphism, rather than a discrete category of model objects. -/
def checkedRoom (checked : Uflia.SExpr.DeclarationPrefix) : Room.{0,0,1} :=
  ⟨Quantified.SExpr.ByteAccepted checked.environment,
    Cat.of (Model checked.environment.signature),
    fun M s => Quantified.SExpr.Surface.Holds checked.environment M s.expression⟩

def ofAcceptedCorridor (checked : Uflia.SExpr.DeclarationPrefix) :
    checkedRoom checked ⟶ room (localSignature checked) :=
  ⟨Family.ofAccepted checked, 𝟭 _, fun M s => Family.ofAccepted_holds checked s M⟩

/-- Only equality arrows between checked prefixes are used here. Each fiber
retains its full ordinary model category. -/
def checkedInstitution : Disc Uflia.SExpr.DeclarationPrefix ⥤ Room.{0,0,1} where
  obj := checkedRoom
  map σ := eqToHom (congrArg checkedRoom σ.down)
  map_id _ := rfl
  map_comp f g := by
    rcases f with ⟨hf⟩
    cases hf
    rcases g with ⟨hg⟩
    cases hg
    rfl

/-- Checked prefixes select genuine varying-sort signatures, not a discrete
replacement for the ambient signature category. -/
def checkedSignatures : Disc Uflia.SExpr.DeclarationPrefix ⥤ Signature where
  obj := localSignature
  map σ := eqToHom (congrArg localSignature σ.down)
  map_id _ := rfl
  map_comp f g := by
    rcases f with ⟨hf⟩
    cases hf
    rcases g with ⟨hg⟩
    cases hg
    rfl

def checkedInst : Inst.{0,0,0,0,1} :=
  ⟨Disc Uflia.SExpr.DeclarationPrefix, checkedInstitution⟩

/-- Natural comparison from the fixed checked-source fibers into the ambient
source families; neither model objects nor ordinary arrows are forgotten. -/
def ofAcceptedComparison : Inst.CoHom checkedInst inst where
  Φ := checkedSignatures
  ρ :=
    { app checked := ofAcceptedCorridor checked
      naturality := by
        intro checked other σ
        rcases σ with ⟨same⟩
        cases same
        change ofAcceptedCorridor checked ≫ institution.map (𝟙 _) =
          (𝟙 _) ≫ ofAcceptedCorridor checked
        rw [institution.map_id]
        exact (Category.comp_id (ofAcceptedCorridor checked)).trans
          (Category.id_comp (ofAcceptedCorridor checked)).symm }

/-- The checked-source decoder factors through the ambient-family institution. -/
def checkedToQuantified : Inst.CoHom checkedInst QuantifiedModels.inst :=
  ofAcceptedComparison.comp toQuantified

end Silmaril.Logic.Smt.Uflia.SortMaps.Source
