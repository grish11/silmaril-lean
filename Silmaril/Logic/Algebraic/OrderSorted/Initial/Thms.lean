module

public import Silmaril.Logic.Algebraic.OrderSorted.Initial.Defs

@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Initial
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured

/-- Every map between empty-sort reducts is unique, even for theories with
arbitrary axioms. No global model-expansion or quotient existence is assumed. -/
@[instance_reducible] def emptyReductHomUnique (T : Theory) (M N : Models T) :
    Unique ((SemanticModels.reduct ordered (emptyTheoryMap T)).obj M ⟶
      (SemanticModels.reduct ordered (emptyTheoryMap T)).obj N) where
  default := { hom := { map := fun s => s.elim, map_op := by intro n w s; exact s.elim } }
  uniq f := by
    apply ObjectProperty.hom_ext
    apply Free.hom_ext
    funext s
    exact s.elim

/-- The actual pointwise free-extension condition along the empty-theory map is
initiality in the category of all coherent models of the given theory. -/
theorem freeAt_iff_initial (T : Theory) (M : Models T) :
    Constraints.FreeAt (SemanticModels.reduct ordered (emptyTheoryMap T)) M ↔
      Nonempty (IsInitial M) :=
  Constraints.freeAt_iff_initial _ _ (fun N => emptyReductHomUnique T M N)

/-- The shared constraint semantics expresses initiality, rather than storing
an initiality witness in each model. -/
theorem initialConstraint_sat_iff (T : Theory) (M : Models T) :
    Constraints.Sat ordered M.obj (initialConstraint T) ↔ Nonempty (IsInitial M) := by
  unfold Constraints.Sat initialConstraint
  rw [ordered.map_id]
  constructor
  · rintro ⟨h, hf⟩
    have he : (⟨M.obj, h⟩ : Models T) = M := by cases M; rfl
    cases he
    exact (freeAt_iff_initial T M).1 hf
  · intro h
    exact ⟨M.property, (freeAt_iff_initial T M).2 h⟩

/-- The genuinely constructed closed free algebra is initial among all coherent
models of the empty presentation. -/
def closedModel_isInitial (A : Signature) : IsInitial (closedModel A) :=
  IsInitial.ofUniqueHom (fun M => ⟨(Free.closed_isInitial A).to M.obj⟩) (by
    intro M f
    apply ObjectProperty.hom_ext
    exact (Free.closed_isInitial A).hom_ext _ _)

theorem closedModel_satisfies (A : Signature) :
    Constraints.Sat ordered (Free.closedModel A) (initialConstraint (emptyPresentation A)) :=
  (initialConstraint_sat_iff _ (closedModel A)).2 ⟨closedModel_isInitial A⟩

/-- Original order-sorted equations embed in the freeness-constraint institution.
The same signatures, coherent models, arbitrary actual homomorphisms and reducts
remain; only the sentence universe is lifted. -/
def equationInclusion : ordered ⟶ institution := Constraints.inclusion.{1,0,0,0,1} ordered

def orderedInst : Inst.{1,0,1,0,1} := ⟨Signature, ordered⟩
def inst : Inst.{1,0,1,0,1} := ⟨Signature, institution⟩
def fromOrderSorted : Inst.CoHom orderedInst inst where
  Φ := 𝟭 _
  ρ := equationInclusion ≫ (Functor.leftUnitor institution).inv

theorem fromOrderSorted_modelExpansive : fromOrderSorted.ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem fromOrderSorted_entails_iff (A : Signature) (H : Set (ULift.{1} (Sentence A)))
    (e : ULift.{1} (Sentence A)) :
    (ordered.obj A).Entails H e ↔
      (institution.obj A).Entails (Sum.inl '' H) (.inl e) :=
  fromOrderSorted.entails_iff fromOrderSorted_modelExpansive A H e

/-- The same satisfaction/consequence statement on the original small sentences. -/
theorem original_entails_iff (A : Signature) (H : Set (Sentence A)) (e : Sentence A) :
    (OrderSorted.institution.obj A).Entails H e ↔
      (institution.obj A).Entails ((fun p => Sum.inl (ULift.up p)) '' H) (.inl (ULift.up e)) := by
  constructor
  · intro h M hm
    exact h M (fun p hp => hm _ ⟨p, hp, rfl⟩)
  · intro h M hm
    apply h M
    rintro _ ⟨p, hp, rfl⟩
    exact hm p hp

end Silmaril.Logic.Algebraic.OrderSorted.Initial
