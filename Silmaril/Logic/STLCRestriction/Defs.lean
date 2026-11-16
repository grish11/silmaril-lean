module

public import Silmaril.Logic.Algebraic.Lambda.Institution

/-! A concrete restriction from all fixed-base public STLC set models to the
inhabited models used by the existing types-to-matching compiler. Syntax is
unchanged; this is not an equivalence of arbitrary lambda/type-system families. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCRestriction
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Algebraic.Lambda
variable {B : Type} {S T : STLCMatching.FixedSignature B}

/-- The backward model component forgets exactly the inhabited-base property. -/
def forgetFunctor (S : STLCMatching.FixedSignature B) :
    STLCMatching.Model S.source ⥤ LambdaModel S.source where
  obj M := ⟨M.toSetModel⟩
  map h := ⟨congrArg (fun M : STLCMatching.Model S.source =>
    (⟨M.toSetModel⟩ : LambdaModel S.source)) h.down⟩

/-- Existing public STLC equations and raw typing sentences are unchanged. -/
def corridor (S : STLCMatching.FixedSignature B) :
    (lambdaInstitution B).obj S ⟶ (STLCMatching.sourceInstitution B).obj S :=
  ⟨id, forgetFunctor S, fun _ _ => Iff.rfl⟩

def natural (B : Type) :
    lambdaInstitution B ⟶ (𝟭 _) ⋙ STLCMatching.sourceInstitution B where
  app := corridor
  naturality := by
    intro S T f
    apply Room.hom_ext
    · rfl
    · rfl

/-- Qualified λ→types: unrestricted fixed-base STLC to its inhabited-model
restriction, with identity signatures/sentences and an actual model reduct. -/
def toInhabited (B : Type) :
    Inst.CoHom (lambdaInst B) (STLCMatching.sourceInst B) :=
  ⟨𝟭 _, natural B⟩

/-- Compose the actual restriction with the existing S/K/I-to-native compiler. -/
def toMatching (B : Type) :
    Inst.CoHom (lambdaInst B) (STLCMatching.targetInst B) :=
  (toInhabited B).comp (STLCMatching.toMatching B)

/-- No operators can force an inhabitant in this actual public STLC signature. -/
def emptySignature (B : Type) : STLCMatching.FixedSignature B := ⟨fun _ _ => Empty⟩

def emptyModel (B : Type) : LambdaModel (emptySignature B).source :=
  ⟨⟨fun _ => Empty, fun o _ => o.elim⟩⟩

end Silmaril.Logic.STLCRestriction
