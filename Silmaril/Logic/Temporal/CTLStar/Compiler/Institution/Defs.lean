module

public import Silmaril.Logic.Temporal.CTLStar.Compiler.Thms
public import Silmaril.Logic.Temporal.CTLStar.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.Compiler.Institution
open CategoryTheory Silmaril.Logic.Institution

def signatureFunctor : CTLStar.Signature ⥤ ModalMu.Signature where
  obj := toMuSig
  map := toMuMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Read the unique action as source accessibility, retaining worlds and point. -/
def decodeModel {S : CTLStar.Signature} (N : ModalMu.Model (toMuSig S)) :
    CTLStar.Model S :=
  ⟨⟨N.World, N.step (), fun a w => w ∈ N.valuation a, N.point⟩⟩

def decodeDiscreteFunctor (S : CTLStar.Signature) :
    ModalMu.Model (toMuSig S) ⥤ CTLStar.Model S where
  obj := decodeModel
  map h := ⟨congrArg decodeModel h.down⟩

def decodeRichFunctor (S : CTLStar.Signature) :
    ModalMu.Model (toMuSig S) ⥤ CTLStar.RichModel S :=
  decodeDiscreteFunctor S ⋙ CTLStar.discreteToRich S

end Silmaril.Logic.Temporal.CTLStar.Compiler.Institution
