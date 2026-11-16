module

public import Silmaril.Logic.Temporal.CTLStar.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar

/-! Independent direct infinite-computation convention from the archived sources.
This is not defined by translating CTL*, CTL or LTL formulas. -/
mutual
def StateFormula.InfiniteHolds {S : Signature} (M : Model S) :
    StateFormula S → M.toModal.World → Prop
  | .atom a, w => M.toModal.valuation a w
  | .bot, _ => False
  | .neg p, w => ¬ p.InfiniteHolds M w
  | .conj p q, w => p.InfiniteHolds M w ∧ q.InfiniteHolds M w
  | .existsPath p, w => ∃ seq : Nat → M.toModal.World,
      seq 0 = w ∧ (∀ n, M.toModal.accessible (seq n) (seq (n+1))) ∧
        p.InfiniteHolds M seq 0

def PathFormula.InfiniteHolds {S : Signature} (M : Model S) :
    PathFormula S → (Nat → M.toModal.World) → Nat → Prop
  | .state p, seq, i => p.InfiniteHolds M (seq i)
  | .neg p, seq, i => ¬ p.InfiniteHolds M seq i
  | .conj p q, seq, i => p.InfiniteHolds M seq i ∧ q.InfiniteHolds M seq i
  | .next p, seq, i => p.InfiniteHolds M seq (i+1)
  | .until p q, seq, i => ∃ d, q.InfiniteHolds M seq (i+d) ∧
      ∀ j, j < d → p.InfiniteHolds M seq (i+j)
end

end Silmaril.Logic.Temporal.CTLStar
