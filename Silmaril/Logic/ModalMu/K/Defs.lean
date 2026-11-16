module

public import Silmaril.Logic.ModalMu.Thms
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
namespace Silmaril.Logic.ModalMu
open CategoryTheory Silmaril.Logic.Institution

/-- Ordinary modal K has a single, unnamed transition relation. -/
def kSignatures : Modal.Signature ⥤ Signature where
  obj S := ⟨S.Atom, Unit⟩
  map f := ⟨f, id⟩

/-- The polarity parameter eliminates arbitrary implication into positive syntax. -/
def encodeK {S : Modal.Signature} : Bool → Modal.Formula S → Formula (kSignatures.obj S) 0
  | b, .atom a => if b then .neg a else .pos a
  | b, .bot => if b then .top else .bot
  | b, .imp p q => if b then .conj (encodeK false p) (encodeK true q)
      else .disj (encodeK true p) (encodeK false q)
  | b, .box p => if b then .diamond () (encodeK true p) else .box () (encodeK false p)

/-- An actual K model expands without altering worlds, relation, atoms or point. -/
def expandK {S : Modal.Signature} (M : Modal.Model S) : Model (kSignatures.obj S) :=
  ⟨M.World, fun _ => M.accessible, fun a => {w | M.valuation a w}, M.point⟩

def forgetK {S : Modal.Signature} (M : Model (kSignatures.obj S)) : Modal.Model S :=
  ⟨M.World, M.step (), fun a w => w ∈ M.valuation a, M.point⟩

/-- On the discrete source model category only identity bounded morphisms are needed. -/
def kModels (S : Modal.Signature) : Model (kSignatures.obj S) ⥤ Modal.Model S where
  obj := forgetK
  map h := eqToHom (congrArg forgetK h.down)

end Silmaril.Logic.ModalMu
