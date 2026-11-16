module

public import Silmaril.Logic.ModalMu.Variables.Thms

@[expose] public section
namespace Silmaril.Logic.ModalMu

/-- Replace atoms by closed formulas, preserving every free fixed-point variable.
Negative literals use the dual replacement; actions have their own explicit map. -/
def Formula.replaceAtoms {S T : Signature} (act : S.Action → T.Action)
    (σ : S.Atom → Formula T 0) : {n : Nat} → Formula S n → Formula T n
  | _, .pos a => (σ a).closedAt _
  | _, .neg a => (σ a).dual.closedAt _
  | _, .bot => .bot
  | _, .top => .top
  | _, .var i => .var i
  | _, .conj p q => .conj (p.replaceAtoms act σ) (q.replaceAtoms act σ)
  | _, .disj p q => .disj (p.replaceAtoms act σ) (q.replaceAtoms act σ)
  | _, .box a p => .box (act a) (p.replaceAtoms act σ)
  | _, .diamond a p => .diamond (act a) (p.replaceAtoms act σ)
  | _, .mu p => .mu (p.replaceAtoms act σ)
  | _, .nu p => .nu (p.replaceAtoms act σ)

/-- Same worlds and point; interpret source atoms by the replacement formulas,
and source actions through the explicit action map. -/
noncomputable def atomReduct {S T : Signature} (act : S.Action → T.Action)
    (σ : S.Atom → Formula T 0) (M : Model T) : Model S where
  World := M.World
  point := M.point
  step a := M.step (act a)
  valuation a := (σ a).denote M emptyEnv

end Silmaril.Logic.ModalMu
