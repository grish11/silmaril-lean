module

public import Silmaril.Logic.Algebraic.Initial.Defs
public import Silmaril.Logic.Institution.Hets.Heterogeneous

@[expose] public section
namespace Silmaril.Logic.Algebraic.Initial
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured

@[ext] theorem algebraHom_ext {A : EQ.Signature} {M N : EQ.Algebra A} (f g : M ⟶ N)
    (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl

/-- Constructor preservation determines every homomorphism by its variables. -/
theorem fold_unique {A : EQ.Signature} {k : Nat} {Γ : Fin k → A.S}
    {M : EQ.Algebra A} (f : termAlgebra A Γ ⟶ M) :
    foldHom M (fun i => f.map (Γ i) (.var i)) = f := by
  apply algebraHom_ext
  funext s t
  induction t with
  | var => rfl
  | app o args ih =>
      exact (congrArg (M.op o) (funext ih)).trans (f.map_op o args).symm

/-- Finite sorted assignments are in bijection with actual algebra homomorphisms. -/
def freeHomEquiv {A : EQ.Signature} {k : Nat} (Γ : Fin k → A.S) (M : EQ.Algebra A) :
    (termAlgebra A Γ ⟶ M) ≃ ((i : Fin k) → M.carrier (Γ i)) where
  toFun f i := f.map (Γ i) (.var i)
  invFun := foldHom M
  left_inv := fold_unique
  right_inv _ := rfl

/-- Naturality of the free universal property under genuine algebra homomorphisms. -/
theorem fold_natural {A : EQ.Signature} {k : Nat} {Γ : Fin k → A.S}
    {M N : EQ.Algebra A} (v : ∀ i, M.carrier (Γ i)) (f : M ⟶ N) :
    foldHom M v ≫ f = foldHom N (fun i => f.map (Γ i) (v i)) := by
  apply algebraHom_ext
  funext s t
  induction t with
  | var => rfl
  | app o args ih =>
      exact (f.map_op o (fun i => (args i).eval M v)).trans
        (congrArg (N.op o) (funext ih))

/-- The empty-generator case is initial, even when some sorts have no terms. -/
def closed_isInitial (A : EQ.Signature) : IsInitial (closedAlgebra A) :=
  IsInitial.ofUniqueHom (fun M => foldHom M (fun i => i.elim0)) (by
    intro M f
    have hv : (fun i : Fin 0 => f.map (closedContext A i) (.var i)) =
        (fun i : Fin 0 => i.elim0) := funext fun i => i.elim0
    exact (fold_unique f).symm.trans (congrArg (foldHom M) hv))

/-- This is the precise premise needed by `FreeAt ↔ IsInitial`.
It is proved for the empty-signature reduct, without a global Exact axiom. -/
@[instance_reducible] def emptyReductHomUnique (T : Theory) (M N : Models T) :
    Unique ((SemanticModels.reduct equational (emptyTheoryMap T)).obj M ⟶
      (SemanticModels.reduct equational (emptyTheoryMap T)).obj N) where
  default := { hom := { map := fun s => s.elim, map_op := fun o => o.elim } }
  uniq f := by
    apply ObjectProperty.hom_ext
    apply algebraHom_ext (A := emptySignature)
    funext s
    exact s.elim

/-- The existing constraint denotes actual initiality in the target theory category. -/
theorem initialConstraint_sat_iff (T : Theory) (M : Models T) :
    Constraints.Sat equational M.obj (initialConstraint T) ↔ Nonempty (IsInitial M) := by
  unfold Constraints.Sat initialConstraint
  rw [equational.map_id]
  constructor
  · rintro ⟨h, hf⟩
    have he : (⟨M.obj, h⟩ : Models T) = M := by cases M; rfl
    cases he
    exact (Constraints.freeAt_iff_initial _ _ (fun N => emptyReductHomUnique T M N)).1 hf
  · intro h
    exact ⟨M.property,
      (Constraints.freeAt_iff_initial _ _ (fun N => emptyReductHomUnique T M N)).2 h⟩

abbrev emptyPresentation (A : EQ.Signature) : Theory := ⟨A, ∅⟩

def closedModel (A : EQ.Signature) : Models (emptyPresentation A) :=
  SemanticModels.emptyModel equational A (closedAlgebra A)

/-- Initiality is lifted to the actual empty-presentation model subcategory. -/
def closedModel_isInitial (A : EQ.Signature) : IsInitial (closedModel A) :=
  IsInitial.ofUniqueHom (fun M => ⟨(closed_isInitial A).to M.obj⟩) (by
    intro M f
    apply ObjectProperty.hom_ext
    exact (closed_isInitial A).hom_ext _ _)

theorem closedModel_satisfies (A : EQ.Signature) :
    Constraints.Sat equational (closedAlgebra A) (initialConstraint (emptyPresentation A)) :=
  (initialConstraint_sat_iff _ (closedModel A)).2 ⟨closedModel_isInitial A⟩

/-- The original equations embed into the existing constraint institution. -/
def equationInclusion : equational ⟶ institution := Constraints.inclusion.{1,0,0,0,1} equational

def equationalInst : Inst.{1,0,1,0,1} := ⟨EQ.Signature, equational⟩
def inst : Inst.{1,0,1,0,1} := ⟨EQ.Signature, institution⟩

def fromEquational : Inst.CoHom equationalInst inst where
  Φ := 𝟭 _
  ρ := equationInclusion ≫ (Functor.leftUnitor institution).inv

theorem fromEquational_modelExpansive : fromEquational.ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem fromEquational_entails_iff (A : EQ.Signature) (H : Set (ULift.{1} (EQ.Equation A)))
    (e : ULift.{1} (EQ.Equation A)) :
    (equational.obj A).Entails H e ↔ (institution.obj A).Entails (Sum.inl '' H) (.inl e) :=
  fromEquational.entails_iff fromEquational_modelExpansive A H e

/-- The same consequence equivalence stated with the original small EQ equations.
`ULift` changes only the sentence universe required by the shared CoHom API. -/
theorem publicEquational_entails_iff (A : EQ.Signature) (H : Set (EQ.Equation A))
    (e : EQ.Equation A) :
    (EQ.institution.obj A).Entails H e ↔
      (institution.obj A).Entails ((fun p => Sum.inl (ULift.up p)) '' H)
        (.inl (ULift.up e)) := by
  constructor
  · intro h M hm
    exact h M (fun p hp => hm _ ⟨p, hp, rfl⟩)
  · intro h M hm
    apply h M
    rintro _ ⟨p, hp, rfl⟩
    exact hm p hp

end Silmaril.Logic.Algebraic.Initial
