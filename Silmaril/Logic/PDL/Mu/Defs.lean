module

public import Silmaril.Logic.PDL.Thms
public import Silmaril.Logic.ModalMu.K.Thms

@[expose] public section
namespace Silmaril.Logic.PDL

mutual
  /-- Closed formula translation, with Boolean negation implemented by μ duality. -/
  def Formula.toMu {S : Signature} : Formula S → ModalMu.Formula S 0
    | .atom a => .pos a
    | .bot => .bot
    | .neg p => p.toMu.dual
    | .conj p q => .conj p.toMu q.toMu
    | .disj p q => .disj p.toMu q.toMu
    | .box a p => (a.toMu p.toMu.dual).dual
    | .diamond a p => a.toMu p.toMu

  /-- Continuation translation. Star binds a fresh set variable; the continuation
  is shifted and test formulas are closed, so neither can be captured. -/
  def Program.toMu {S : Signature} : Program S → {n : Nat} →
      ModalMu.Formula S n → ModalMu.Formula S n
    | .action a, _, c => .diamond a c
    | .seq a b, _, c => a.toMu (b.toMu c)
    | .choice a b, _, c => .disj (a.toMu c) (b.toMu c)
    | .star a, _, c => .mu (.disj c.shift (a.toMu (.var 0)))
    | .test p, n, c => .conj (p.toMu.closedAt n) c
end

end Silmaril.Logic.PDL
