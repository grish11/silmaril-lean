module

public import Silmaril.Logic.Algebraic.Lambda.Signatures

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Lambda
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc

namespace Unrestricted
variable {B : Type} {S T U : STLCMatching.FixedSignature B}

def pull (f : S ⟶ T) (M : STLC.SetModel T.source) : STLC.SetModel S.source :=
  ⟨M.base, fun o args => M.op (f.operators o) args⟩

theorem eval_map (f : S ⟶ T) (M : STLC.SetModel T.source)
    {Γ : Ctx B} {τ : Ty B} (t : Term S.source Γ τ)
    (ρ : Tuple (STLC.carrier M.base) Γ) :
    STLC.eval M (t.mapOp f.operators) ρ = STLC.eval (pull f M) t ρ := by
  refine Term.rec (S := S.source) (motive := fun Γ τ t => ∀ ρ : Tuple (STLC.carrier M.base) Γ,
    STLC.eval M (t.mapOp f.operators) ρ = STLC.eval (pull f M) t ρ) ?_ ?_ ?_ ?_ t ρ
  · intro Γ τ x ρ
    rfl
  · intro Γ a b t ih ρ
    funext x
    exact ih (Tuple.cons x ρ)
  · intro Γ a b t u iht ihu ρ
    exact congrArg₂ (fun f x => f x) (iht ρ) (ihu ρ)
  · intro Γ as τ o args ih ρ
    exact congrArg (M.op (f.operators o)) (funext fun a => funext fun v => ih a v ρ)

theorem satisfaction (f : S ⟶ T) (M : STLC.SetModel T.source)
    (p : STLC.Sentence S.source) :
    STLC.Sat M (STLCMatching.FixedHom.sentence f p) ↔ STLC.Sat (pull f M) p := by
  cases p with
  | typing Γ t τ =>
      classical
      change Raw.HasType (S := T.source) Γ (STLCMatching.FixedHom.raw f t) τ ↔ Raw.HasType (S := S.source) Γ t τ
      rw [← Raw.infer_eq_some, ← Raw.infer_eq_some, STLCMatching.FixedHom.infer_raw]
  | equation t u =>
      simp only [STLCMatching.FixedHom.sentence, STLC.Sat, eval_map]
      rfl

theorem pull_id (M : STLC.SetModel S.source) : pull (𝟙 S) M = M := by
  cases M
  rfl

theorem pull_comp (f : S ⟶ T) (g : T ⟶ U) (M : STLC.SetModel U.source) :
    pull (f ≫ g) M = pull f (pull g M) := rfl

end Unrestricted

/-- All actual set models; equality arrows live in the small hom universe. -/
structure LambdaModel (S : Signature) where
  toSetModel : STLC.SetModel S

instance (S : Signature) : Category (LambdaModel S) where
  Hom M N := PLift (M = N)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

instance {S : Signature} (M N : LambdaModel S) : Subsingleton (M ⟶ N) :=
  inferInstanceAs (Subsingleton (PLift (M = N)))

def modelReduct (A : EQ.Signature) : LambdaModel (signature A) ⥤ EQ.Algebra A where
  obj M := reduct M.toSetModel
  map h := eqToHom (congrArg (fun M => reduct M.toSetModel) h.down)
  map_id _ := rfl
  map_comp f g := by cases f.down; cases g.down; rfl

theorem reduct_pull {B : Type} {A D : FixedSignature B} (f : A ⟶ D)
    (M : STLC.SetModel D.lambda.source) :
    reduct (Unrestricted.pull f.lambda M) =
      (EQ.Algebra.reduct f.equational).obj (reduct M) := rfl

end Silmaril.Logic.Algebraic.Lambda
