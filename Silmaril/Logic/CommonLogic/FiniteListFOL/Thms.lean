module

public import Silmaril.Logic.CommonLogic.FiniteListFOL.Defs
public import Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL

@[expose] public section
namespace Silmaril.Logic.CommonLogic.FiniteListFOL
open Silmaril.Logic.FirstOrder
open CategoryTheory

theorem append_evaluation {S : Core.Signature} (M : Model S)
    (xs ys : List (D M.obj)) :
    append M.obj (FiniteLists.evaluationEquiv M.obj xs)
      (FiniteLists.evaluationEquiv M.obj ys) =
        FiniteLists.evaluationEquiv M.obj (xs ++ ys) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.append_evaluation M xs ys

@[simp] theorem decode_expand {S : Core.Signature} (M : Core.Model S) : decode (expand M) = M :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.decode_expand M

noncomputable def decodeHom {S : Core.Signature} {M N : Model S} (h : M ⟶ N) :
    decode M ⟶ decode N := Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.decodeHom h

noncomputable def models (S : Core.Signature) : Model S ⥤ Core.Model S :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.models S

theorem decode_reduct {S T : Core.Signature} (f : S ⟶ T) (M : Model T) :
    decode ((reduct f).obj M) = (Core.Model.reduct f).obj (decode M) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.decode_reduct f M

theorem signatureMap_id (S : Core.Signature) : signatureMap (𝟙 S) = 𝟙 (signature S) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.signatureMap_id S

theorem signatureMap_comp {S T U : Core.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    signatureMap (f ≫ g) = signatureMap f ≫ signatureMap g :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.signatureMap_comp f g

def signatures : Core.Signature ⥤ FiniteLists.Signature where
  obj := signature
  map := signatureMap
  map_id := signatureMap_id
  map_comp := signatureMap_comp

theorem reduct_id (S : Core.Signature) : reduct (𝟙 S) = 𝟭 (Model S) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.reduct_id S

theorem reduct_comp {S T U : Core.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    reduct (f ≫ g) = reduct g ⋙ reduct f :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.reduct_comp f g

theorem corridor_id (S : Core.Signature) : corridor (𝟙 S) = 𝟙 (room S) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.corridor_id S

theorem corridor_comp {S T U : Core.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    corridor (f ≫ g) = corridor f ≫ corridor g :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.corridor_comp f g

/-- All public FOL sentences and full constrained FOL model categories. -/
def institution : Core.Signature ⥤ Silmaril.Logic.Institution.Room.{0,0,1} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

def inst : Silmaril.Logic.Institution.Inst.{1,0,0,0,1} := ⟨Core.Signature, institution⟩

theorem models_natural {S T : Core.Signature} (f : S ⟶ T) :
    reduct f ⋙ models S = models T ⋙ Core.Model.reduct f :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOL.models_natural f

end Silmaril.Logic.CommonLogic.FiniteListFOL
