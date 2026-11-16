module

public import Silmaril.Logic.Algebraic.Lambda.Models
public import Silmaril.Logic.STLCMatching.Institution
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.Lambda
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
variable {B : Type} {S T U : STLCMatching.FixedSignature B}

theorem LambdaModel.ext {S : Signature} {M N : LambdaModel S}
    (h : M.toSetModel = N.toSetModel) : M = N := by
  cases M
  cases N
  cases h
  rfl

def pullModel (f : S ⟶ T) (M : LambdaModel T.source) : LambdaModel S.source :=
  ⟨Unrestricted.pull f M.toSetModel⟩

def pullFunctor (f : S ⟶ T) : LambdaModel T.source ⥤ LambdaModel S.source where
  obj := pullModel f
  map h := ⟨congrArg (pullModel f) h.down⟩

private theorem model_arrow_hext {S : Signature} {M M' N N' : LambdaModel S}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N') : HEq f g := by
  cases hM
  cases hN
  exact heq_of_eq (Subsingleton.elim _ _)

theorem pullFunctor_id : pullFunctor (𝟙 S) = 𝟭 (LambdaModel S.source) := by
  have h : ∀ M : LambdaModel S.source, pullModel (𝟙 S) M = M :=
    fun M => LambdaModel.ext (Unrestricted.pull_id M.toSetModel)
  apply Functor.hext h
  intro M N f
  exact model_arrow_hext (h M) (h N) _ _

theorem pullFunctor_comp (f : S ⟶ T) (g : T ⟶ U) :
    pullFunctor (f ≫ g) = pullFunctor g ⋙ pullFunctor f := by
  apply Functor.hext (fun _ => rfl)
  intro M N h
  exact heq_of_eq (Subsingleton.elim _ _)

/-- Unrestricted public STLC set semantics, with equality model arrows. -/
def lambdaRoom (S : STLCMatching.FixedSignature B) : Room.{0,0,1} :=
  ⟨STLC.Sentence S.source, Cat.of (LambdaModel S.source), fun M => STLC.Sat M.toSetModel⟩

def lambdaInstitution (B : Type) : STLCMatching.FixedSignature B ⥤ Room.{0,0,1} where
  obj := lambdaRoom
  map f := ⟨STLCMatching.FixedHom.sentence f, pullFunctor f,
    fun M => Unrestricted.satisfaction f M.toSetModel⟩
  map_id _ := Room.hom_ext (funext STLCMatching.FixedHom.sentence_id) pullFunctor_id
  map_comp f g := Room.hom_ext (funext (STLCMatching.FixedHom.sentence_comp f g))
    (pullFunctor_comp f g)

/-- Signature restriction only: every public EQ model and homomorphism is retained. -/
def equationalInstitution (B : Type) : FixedSignature B ⥤ Room.{0,0,1} :=
  toEquational B ⋙ EQ.institution

def equationalInst (B : Type) : Inst := ⟨FixedSignature B, equationalInstitution B⟩
def lambdaInst (B : Type) : Inst := ⟨STLCMatching.FixedSignature B, lambdaInstitution B⟩

def equationCorridor (A : FixedSignature B) :
    (equationalInstitution B).obj A ⟶ (lambdaInstitution B).obj A.lambda :=
  ⟨equation, modelReduct A.equational, fun M e => satisfies_equation (A := A.equational) M.toSetModel e⟩

theorem modelReduct_naturality {A D : FixedSignature B} (f : A ⟶ D) :
    modelReduct D.equational ⋙ EQ.Algebra.reduct f.equational =
      pullFunctor f.lambda ⋙ modelReduct A.equational := by
  apply Functor.hext (F := modelReduct D.equational ⋙ EQ.Algebra.reduct f.equational)
    (G := pullFunctor f.lambda ⋙ modelReduct A.equational)
    (fun M => (reduct_pull f M.toSetModel).symm)
  intro M N h
  cases h.down
  rfl

def equationNatural (B : Type) :
    equationalInstitution B ⟶ toLambda B ⋙ lambdaInstitution B where
  app := equationCorridor
  naturality := by
    intro A D f
    apply Room.hom_ext
    · exact funext fun e => (equation_naturality f e).symm
    · exact modelReduct_naturality f

/-- Actual first-order equations enter lambda equations over fixed base sorts. -/
def toSTLC (B : Type) : Inst.CoHom (equationalInst B) (lambdaInst B) :=
  ⟨toLambda B, equationNatural B⟩

theorem toSTLC_modelExpansive (B : Type) : (toSTLC B).ModelExpansive := by
  intro A M
  exact ⟨⟨expand M⟩, reduct_expand M⟩

theorem entails_iff {A : FixedSignature B} (H : Set (EQ.Equation A.equational))
    (e : EQ.Equation A.equational) :
    (EQ.room A.equational).Entails H e ↔
      (lambdaRoom A.lambda).Entails (equation '' H) (equation e) :=
  (toSTLC B).entails_iff (toSTLC_modelExpansive B) A H e

theorem sat_iff {A : FixedSignature B} (H : Set (EQ.Equation A.equational)) :
    (∃ M : EQ.Algebra A.equational, ∀ e ∈ H, e.Holds M) ↔
      ∃ M : STLC.SetModel (signature A.equational), ∀ e ∈ H, STLC.Sat M (equation e) := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨expand M, fun e he => ?_⟩
    apply (satisfies_equation _ e).2
    simpa only [reduct_expand] using h e he
  · rintro ⟨M, h⟩
    exact ⟨reduct M, fun e he => (satisfies_equation M e).1 (h e he)⟩

theorem unsat_iff {A : FixedSignature B} (H : Set (EQ.Equation A.equational)) :
    (¬ ∃ M : EQ.Algebra A.equational, ∀ e ∈ H, e.Holds M) ↔
      ¬ ∃ M : STLC.SetModel (signature A.equational), ∀ e ∈ H, STLC.Sat M (equation e) :=
  not_congr (sat_iff H)

end Silmaril.Logic.Algebraic.Lambda
