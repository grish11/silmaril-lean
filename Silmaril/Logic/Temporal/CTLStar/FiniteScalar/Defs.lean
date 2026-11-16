module

public import Silmaril.Logic.Temporal.CTLStar.FiniteTableau.Thms
public import Silmaril.Logic.Temporal.FiniteAutomaton.CTLStar

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.FiniteScalar
open LTL.Tableau Buchi.Automaton ModalMu

/-- Finite occurrence assignments, encoded by the shared finite equivalence.
Initiality is exactly the root bit; edges and endpoints retain actual guards. -/
def pack {A : Type} (s : Shape) (edge : State s → State s → Guard A)
    (last : State s → Guard A) : FiniteAutomaton.Symbolic A (Fintype.card (State s)) where
  initial := {q | bit ((stateEquiv s).symm q) = true}
  guard q r := edge ((stateEquiv s).symm q) ((stateEquiv s).symm r)
  terminal q := last ((stateEquiv s).symm q)

def automaton {A : Type} (p : NNF.Formula A) :=
  pack (FiniteTableau.shape p) (FiniteTableau.transition p) (FiniteTableau.terminal p)

/-- Closed scalar modal μ syntax on the original world and action signature. -/
def formula {S : ModalMu.Signature} (p : NNF.Formula S.Atom) (a : S.Action) : ModalMu.Formula S 0 :=
  FiniteAutomaton.formula (automaton p) a

end Silmaril.Logic.Temporal.CTLStar.FiniteScalar
