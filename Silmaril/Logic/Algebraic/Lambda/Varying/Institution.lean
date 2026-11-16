module

public import Silmaril.Logic.Algebraic.Lambda.Varying.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Lambda.Varying
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube

/-- Every public sort map is admitted, including identification of sorts. -/
def toLambda : EQ.Signature ⥤ STLCEquations.Language where
  obj := language
  map := signatureMap
  map_id := signatureMap_identity
  map_comp := signatureMap_comp

def equationCorridor (A : EQ.Signature) : EQ.room A ⟶ STLCEquations.room (language A) :=
  ⟨compile, modelReduct A, fun M e => satisfaction M.toSetModel e⟩

def equationNatural : EQ.institution ⟶ toLambda ⋙ STLCEquations.institution where
  app := equationCorridor
  naturality := by
    intro A D f
    apply Room.hom_ext
    · exact funext fun e => (compile_naturality f e).symm
    · exact modelReduct_naturality f

/-- Full public EQ to typed lambda equations, with actual whole model reducts. -/
def toSTLC : Inst.CoHom EQ.inst STLCEquations.inst := ⟨toLambda, equationNatural⟩

theorem toSTLC_modelExpansive : toSTLC.ModelExpansive := by
  intro A M
  exact ⟨⟨expand M⟩, reduct_expand M⟩

theorem entails_iff (A : EQ.Signature) (H : Set (EQ.Equation A)) (e : EQ.Equation A) :
    (EQ.room A).Entails H e ↔
      (STLCEquations.room (language A)).Entails (compile '' H) (compile e) :=
  toSTLC.entails_iff toSTLC_modelExpansive A H e

theorem sat_iff (A : EQ.Signature) (H : Set (EQ.Equation A)) :
    (∃ M : EQ.Algebra A, ∀ e ∈ H, e.Holds M) ↔
      ∃ M : STLC.SetModel (signature A), ∀ e ∈ H, STLCEquations.Holds M (compile e) := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨expand M, fun e he => ?_⟩
    apply (satisfaction _ e).2
    simpa only [reduct_expand] using h e he
  · rintro ⟨M, h⟩
    exact ⟨reduct M, fun e he => (satisfaction M e).1 (h e he)⟩

theorem unsat_iff (A : EQ.Signature) (H : Set (EQ.Equation A)) :
    (¬ ∃ M : EQ.Algebra A, ∀ e ∈ H, e.Holds M) ↔
      ¬ ∃ M : STLC.SetModel (signature A), ∀ e ∈ H, STLCEquations.Holds M (compile e) :=
  not_congr (sat_iff A H)

end Silmaril.Logic.Algebraic.Lambda.Varying
