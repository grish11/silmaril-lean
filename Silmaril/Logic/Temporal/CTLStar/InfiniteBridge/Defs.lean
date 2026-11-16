module

public import Silmaril.Logic.Temporal.CTLStar.NNF.Thms
public import Silmaril.Logic.Temporal.LTL.Tableau.Modal

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.NNF

/-- Erase the next distinction for infinite words only. Until and Release,
including the existing Büchi fairness obligations, retain their constructors. -/
def Formula.toInfinite {A : Type} : Formula A → LTL.NNF.Formula A
  | .pos a => .pos a
  | .neg a => .neg a
  | .bot => .bot
  | .top => .top
  | .conj p q => .conj p.toInfinite q.toInfinite
  | .disj p q => .disj p.toInfinite q.toInfinite
  | .strongNext p => .next p.toInfinite
  | .weakNext p => .next p.toInfinite
  | .until p q => .until p.toInfinite q.toInfinite
  | .release p q => .release p.toInfinite q.toInfinite

end Silmaril.Logic.Temporal.CTLStar.NNF

noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.InfiniteBridge

/-- Reuse the actual generalized Büchi automaton, including its recurrence
family. No second transition table or acceptance oracle is introduced. -/
def automaton {A : Type} (p : NNF.Formula A) := LTL.Tableau.automaton p.toInfinite

/-- Actual closed scalar modal μ syntax on the original graph. -/
def formula {S : ModalMu.Signature} (p : NNF.Formula S.Atom) (a : S.Action) :
    ModalMu.Formula S 0 := LTL.Tableau.formula p.toInfinite a

end Silmaril.Logic.Temporal.CTLStar.InfiniteBridge
