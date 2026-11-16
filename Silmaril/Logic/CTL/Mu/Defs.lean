module

public import Silmaril.Logic.CTL.Thms
public import Silmaril.Logic.ModalMu
public import Silmaril.Logic.ModalMu.Variables.Thms

@[expose] public section
namespace Silmaril.Logic.CTL
open CategoryTheory

/-- The atom functor is the public K-to-modal-μ signature functor. -/
abbrev muSignatures := ModalMu.kSignatures

/-- Closed CTL subformulas are shifted before entering each fresh μ/ν binder. -/
def Formula.toMu {S : Signature} : Formula S → ModalMu.Formula (muSignatures.obj S) 0
  | .atom a => .pos a
  | .bot => .bot
  | .neg p => p.toMu.dual
  | .conj p q => .conj p.toMu q.toMu
  | .ex p => .diamond () p.toMu
  | .eu p q => .mu (.disj q.toMu.shift (.conj p.toMu.shift (.diamond () (.var 0))))
  | .eg p => .nu (.conj p.toMu.shift (.diamond () (.var 0)))

/-- Every target model has its actual relation/valuation CTL reduct. -/
def forgetMu {S : Signature} (M : ModalMu.Model (muSignatures.obj S)) : Model S :=
  ⟨ModalMu.forgetK M⟩

def muModels (S : Signature) : ModalMu.Model (muSignatures.obj S) ⥤ Model S where
  obj := forgetMu
  map h := ⟨congrArg forgetMu h.down⟩

def expandMu {S : Signature} (M : Model S) : ModalMu.Model (muSignatures.obj S) :=
  ModalMu.expandK M.toModal

end Silmaril.Logic.CTL
