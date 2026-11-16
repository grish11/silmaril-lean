module

public import Silmaril.Logic.STLCRestriction.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCRestriction.Examples
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc
open Algebraic.Lambda

def bit : Ty Unit := .base ()

inductive SourceOp : List (Ty Unit) → Ty Unit → Type
  | left : SourceOp [] bit
  | right : SourceOp [] bit

inductive TargetOp : List (Ty Unit) → Ty Unit → Type
  | only : TargetOp [] bit

def source : STLCMatching.FixedSignature Unit := ⟨SourceOp⟩
def target : STLCMatching.FixedSignature Unit := ⟨TargetOp⟩

/-- Distinct actual constant symbols may collapse under a profile-preserving map. -/
def collapse : source ⟶ target := ⟨fun o => match o with
  | .left => .only
  | .right => .only⟩

theorem collapse_is_noninjective :
    collapse.operators SourceOp.left = collapse.operators SourceOp.right ∧
      SourceOp.left ≠ SourceOp.right := ⟨rfl, by intro h; cases h⟩

def targetModel : STLCMatching.Model target.source :=
  ⟨⟨fun _ => Bool, fun o _ => match o with | .only => false⟩, fun _ => ⟨false⟩⟩

def separatedModel : LambdaModel source.source :=
  ⟨⟨fun _ => Bool, fun o _ => match o with | .left => false | .right => true⟩⟩

def constantsEqual : STLC.Sentence source.source :=
  .equation (Γ := []) (.op SourceOp.left Tuple.nil) (.op SourceOp.right Tuple.nil)

theorem separated_constants_rejected :
    ¬ STLC.Sat separatedModel.toSetModel constantsEqual := by
  intro h
  have he := h Tuple.nil
  change false = true at he
  cases he

theorem collapsed_constants_hold :
    STLC.Sat targetModel.toSetModel (STLCMatching.FixedHom.sentence collapse constantsEqual) := by
  intro _
  rfl

/-- Both concrete reduct paths agree, including collapsed operator interpretation. -/
theorem actual_reduct_square :
    (forgetFunctor source).obj ((STLCMatching.FixedHom.pullFunctor collapse).obj targetModel) =
      (pullFunctor collapse).obj ((forgetFunctor target).obj targetModel) := rfl

theorem collapse_satisfaction :
    STLC.Sat targetModel.toSetModel (STLCMatching.FixedHom.sentence collapse constantsEqual) ↔
      STLC.Sat ((pullFunctor collapse).obj ((forgetFunctor target).obj targetModel)).toSetModel
        constantsEqual :=
  Unrestricted.satisfaction collapse targetModel.toSetModel constantsEqual

def beta : STLC.Sentence source.source :=
  .equation (Γ := [bit]) (.app (.lam (.var .zero)) (.var .zero)) (.var .zero)

theorem beta_unrestricted (M : LambdaModel source.source) : STLC.Sat M.toSetModel beta := by
  intro _
  rfl

theorem beta_inhabited (M : STLCMatching.Model source.source) : STLC.Sat M.toSetModel beta :=
  beta_unrestricted ((forgetFunctor source).obj M)

theorem beta_compiled (M : STLCMatching.Model source.source) :
    (STLCMatching.targetRoom source).Sat M (STLCMatching.translate beta) :=
  (matching_satisfaction M beta).mpr (beta_unrestricted ((forgetFunctor source).obj M))

def wellTyped : STLC.Sentence source.source := .typing [bit] (.var 0) bit

def selfApplication : STLC.Sentence source.source :=
  .typing [bit] (.app (.var 0) (.var 0)) bit

theorem typing_survives_restriction (M : STLCMatching.Model source.source) :
    (lambdaRoom source).Sat ((forgetFunctor source).obj M) wellTyped ∧
      (STLCMatching.sourceRoom source).Sat M wellTyped := by
  constructor <;> exact Raw.HasType.var (by rfl)

theorem bad_typing_rejected (M : STLCMatching.Model source.source) :
    ¬ (STLCMatching.targetRoom source).Sat M (STLCMatching.translate selfApplication) := by
  rw [matching_satisfaction]
  exact Raw.HasType.not_app_var_self

/-- An actual unrestricted model with an empty used base has no target expansion. -/
theorem empty_unit_no_expansion :
    ¬ ∃ N : STLCMatching.Model (emptySignature Unit).source,
      (forgetFunctor (emptySignature Unit)).obj N = emptyModel Unit := by
  rw [expansion_iff]
  intro h
  obtain ⟨x⟩ := h ()
  exact x.elim

theorem unit_not_modelExpansive : ¬ (toInhabited Unit).ModelExpansive :=
  not_modelExpansive Unit

theorem empty_base_universe_modelExpansive : (toInhabited Empty).ModelExpansive :=
  (modelExpansive_iff_isEmpty Empty).mpr inferInstance

end Silmaril.Logic.STLCRestriction.Examples
