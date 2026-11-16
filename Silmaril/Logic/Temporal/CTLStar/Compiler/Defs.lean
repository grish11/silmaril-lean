module

public import Silmaril.Logic.Temporal.CTLStar.UniversalPath.Thms
public import Silmaril.Logic.ModalMu.AtomSubstitution.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.Compiler
open CategoryTheory

/-- One scalar action for the original source accessibility relation. -/
abbrev toMuSig (S : CTLStar.Signature) : ModalMu.Signature := ⟨S.Atom, Unit⟩

abbrev Closed (S : CTLStar.Signature) := ModalMu.Formula (toMuSig S) 0

def toMuMap {S T : CTLStar.Signature} (f : S ⟶ T) : toMuSig S ⟶ toMuSig T :=
  ⟨f, id⟩

/-- Fixed original worlds, valuation and point; no formula-dependent model. -/
abbrev encodeModel {S : CTLStar.Signature} (M : CTLStar.Model S) : ModalMu.Model (toMuSig S) where
  World := M.toModal.World
  point := M.toModal.point
  step _ := M.toModal.accessible
  valuation a := {w | M.toModal.valuation a w}

mutual
/-- Fused state compilation; all recursive calls follow direct source children. -/
def compileState {S : CTLStar.Signature} : StateFormula S → Closed S
  | .atom a => .pos a
  | .bot => .bot
  | .neg p => (compileState p).dual
  | .conj p q => .conj (compileState p) (compileState q)
  | .existsPath p =>
      ModalMu.Formula.replaceAtoms (S := ⟨Closed S, Unit⟩) (T := toMuSig S) id id
        (MaximalPath.formula (S := ⟨Closed S, Unit⟩) (compilePathNNF false p) ())

/-- Normalize path polarity while compiling embedded state leaves. The output
atoms are already closed target formulas, so replacement is total identity. -/
def compilePathNNF {S : CTLStar.Signature} : Bool → PathFormula S → NNF.Formula (Closed S)
  | false, .state p => .pos (compileState p)
  | true, .state p => .neg (compileState p)
  | b, .neg p => compilePathNNF (!b) p
  | false, .conj p q => .conj (compilePathNNF false p) (compilePathNNF false q)
  | true, .conj p q => .disj (compilePathNNF true p) (compilePathNNF true q)
  | false, .next p => .strongNext (compilePathNNF false p)
  | true, .next p => .weakNext (compilePathNNF true p)
  | false, .until p q => .until (compilePathNNF false p) (compilePathNNF false q)
  | true, .until p q => .release (compilePathNNF true p) (compilePathNNF true q)
end

end Silmaril.Logic.Temporal.CTLStar.Compiler
