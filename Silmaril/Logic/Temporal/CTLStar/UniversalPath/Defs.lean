module

public import Silmaril.Logic.Temporal.CTLStar.MaximalPath.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.UniversalPath

/-- No finite or infinite accepting counterexample path for the temporal dual. -/
def AllPaths {A W : Type} (p : NNF.Formula A) (R : W → W → Prop)
    (label : W → A → Prop) (w : W) : Prop :=
  ¬ MaximalPath.AcceptsPath p.dual R label w

/-- Actual closed scalar syntax: complement the existential counterexample
compiler. Structural dual swaps literals, modalities and fixed point binders. -/
def allFormula {S : ModalMu.Signature} (p : NNF.Formula S.Atom) (a : S.Action) :
    ModalMu.Formula S 0 := (MaximalPath.formula p.dual a).dual

end Silmaril.Logic.Temporal.CTLStar.UniversalPath
