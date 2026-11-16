module

public import Silmaril.Logic.Institution.Structured.Theories.Thms
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured
open CategoryTheory Silmaril.Logic.Institution
universe u
noncomputable section
variable {Sign : Type u} [Category.{u} Sign]

/-- Assembling all local consequences yields the original global closure. -/
def counitHom (I : ClassicInstitution.{u,u,u,u,u} Sign) (P : StructuredTheory I) :
    (R I).obj ((J I).obj P) ⟶ P :=
  ⟨𝟙 P.sig, by
    intro φ hφ
    rcases φ with ⟨node, φ⟩
    change ⟨node, φ⟩ ∈ (room I P.sig).closure P.axioms at hφ
    change ⟨node, I.Sen.map (𝟙 _) φ⟩ ∈ (room I P.sig).closure P.axioms
    simpa only [I.Sen.map_id_apply] using hφ⟩

/-- The original axioms entail every original axiom viewed in its node closure. -/
def counitInv (I : ClassicInstitution.{u,u,u,u,u} Sign) (P : StructuredTheory I) :
    P ⟶ (R I).obj ((J I).obj P) :=
  ⟨𝟙 P.sig, by
    intro φ hφ
    apply (room I _).subset_closure
    rcases φ with ⟨node, φ⟩
    change I.Sen.map (𝟙 _) φ ∈ nodeConsequences I P node
    simp only [I.Sen.map_id_apply]
    exact (room I P.sig).subset_closure P.axioms hφ⟩

/-- The counit component is a genuine isomorphism of semantic presentations. -/
def counitIso (I : ClassicInstitution.{u,u,u,u,u} Sign) (P : StructuredTheory I) :
    (R I).obj ((J I).obj P) ≅ P where
  hom := counitHom I P
  inv := counitInv I P
  hom_inv_id := Spec.hom_ext (Category.comp_id _)
  inv_hom_id := Spec.hom_ext (Category.comp_id _)

/-- Transpose a map from a union of axioms by reading its conclusion nodewise. -/
def toDiagramHom (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (D : CoDiagram.{u,u} (Spec I.toRoomFunctor)) (P : StructuredTheory I)
    (f : (R I).obj D ⟶ P) : D ⟶ (J I).obj P where
  Φ := f.sig.Φ
  ρ := {
    app := fun node => ⟨f.sig.ρ.app node, fun φ hφ =>
      (I.toRoomFunctor.obj _).subset_closure _ (f.mapsTo (show ⟨node, φ⟩ ∈ (unionTheory I D).axioms from hφ))⟩
    naturality := fun _ _ g => Spec.hom_ext (f.sig.ρ.naturality g) }

/-- Transpose a diagram map by assembling its local axioms and using the counit. -/
def fromDiagramHom (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (D : CoDiagram.{u,u} (Spec I.toRoomFunctor)) (P : StructuredTheory I)
    (f : D ⟶ (J I).obj P) : (R I).obj D ⟶ P where
  sig := {
    Φ := f.Φ
    ρ := {
      app := fun node => (f.ρ.app node).sig
      naturality := fun _ _ g => congrArg Spec.Hom.sig (f.ρ.naturality g) } }
  mapsTo := by
    intro φ hφ
    have h := (f.ρ.app φ.1).mapsTo hφ
    change _ ∈ (I.toRoomFunctor.obj _).closure (nodeConsequences I P (f.Φ.obj φ.1)) at h
    rw [nodeConsequences_closed] at h
    exact h

/-- The hom equivalence of the actual union/consequence constructions. -/
def theoryHomEquiv (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (D : CoDiagram.{u,u} (Spec I.toRoomFunctor)) (P : StructuredTheory I) :
    ((R I).obj D ⟶ P) ≃ (D ⟶ (J I).obj P) where
  toFun := toDiagramHom I D P
  invFun := fromDiagramHom I D P
  left_inv _ := rfl
  right_inv _ := rfl

/-- Union is left adjoint to the fully faithful diagram-of-consequences functor
(Durán–Meseguer, Proposition 4.8). -/
def theoryAdjunction (I : ClassicInstitution.{u,u,u,u,u} Sign) : R I ⊣ J I :=
  Adjunction.mkOfHomEquiv {
    homEquiv := theoryHomEquiv I
    homEquiv_naturality_left_symm := by
      intro D E P f g
      rfl
    homEquiv_naturality_right := by
      intro D P Q f g
      rfl }


/-- The counit of the constructed adjunction is the semantic closure isomorphism. -/
theorem theoryAdjunction_counit (I : ClassicInstitution.{u,u,u,u,u} Sign)
    (P : StructuredTheory I) :
    (theoryAdjunction I).counit.app P = (counitIso I P).hom := by
  apply Spec.hom_ext
  rfl

instance theoryAdjunction_counit_isIso (I : ClassicInstitution.{u,u,u,u,u} Sign) :
    IsIso (theoryAdjunction I).counit := by
  have : ∀ P, IsIso ((theoryAdjunction I).counit.app P) := by
    intro P
    rw [theoryAdjunction_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The actual consequence-diagram functor is fully faithful. -/
def J_fullyFaithful (I : ClassicInstitution.{u,u,u,u,u} Sign) : (J I).FullyFaithful :=
  (theoryAdjunction I).fullyFaithfulROfIsIsoCounit

end
end Silmaril.Logic.Institution.Structured
