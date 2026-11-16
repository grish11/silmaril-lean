module

public import Silmaril.Logic.Temporal.CTLStar.FiniteScalar.Thms
public import Silmaril.Logic.Temporal.CTLStar.InfiniteBridge.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.MaximalPath

/-- Choose a finite accepting run or an infinite Büchi accepting run. Each
branch still reads one complete coherent original path. -/
def AcceptsPath {A W : Type} (p : NNF.Formula A) (R : W → W → Prop)
    (label : W → A → Prop) (w : W) : Prop :=
  FiniteAutomaton.AcceptsPath (FiniteScalar.automaton p) R label w ∨
    (InfiniteBridge.automaton p).AcceptsPath R label w

/-- Actual scalar disjunction of the two already proved path compilers. -/
def formula {S : ModalMu.Signature} (p : NNF.Formula S.Atom) (a : S.Action) :
    ModalMu.Formula S 0 :=
  .disj (FiniteScalar.formula p a) (InfiniteBridge.formula p a)

end Silmaril.Logic.Temporal.CTLStar.MaximalPath
