module

public import Silmaril.Logic.STLCEquations.Thms

/-! Public intrinsically typed lambda terms and full-function set models, with
arbitrary base-type maps. Sentences are equations only: raw typing reflection
cannot admit maps that identify distinct source base types. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCEquations
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Silmaril.Calculi.LambdaCube.STLC
open Cslib.LambdaCalculus.LocallyNameless.Stlc

def room (S : Language) : Room.{0,0,1} :=
  ⟨Sentence S, Cat.of (Model S), fun M => Holds M.toSetModel⟩

/-- The actual sentence action and whole model reduct functors satisfy both laws. -/
def institution : Language ⥤ Room.{0,0,1} where
  obj := room
  map f := ⟨mapSentence f, reductFunctor f, fun M p => satisfaction f M.toSetModel p⟩
  map_id S := Room.hom_ext (funext mapSentence_identity) (reductFunctor_identity S)
  map_comp f g := Room.hom_ext (funext (mapSentence_comp f g)) (reductFunctor_comp f g)

def inst : Inst := ⟨Language, institution⟩


end Silmaril.Logic.STLCEquations
