module

public import Silmaril.Logic.ModalMu.Variables.Thms

@[expose] public section
namespace Silmaril.Logic.ModalMu

/-- Parallel positive formula substitution, lifted under either fixed-point binder. -/
def liftSubstitution {S : Signature} {n m : Nat} (σ : Fin n → Formula S m) :
    Fin (n+1) → Formula S (m+1) := Fin.cases (.var 0) (fun i => (σ i).shift)

def Formula.substitute {S : Signature} : {n m : Nat} →
    (Fin n → Formula S m) → Formula S n → Formula S m
  | _, _, _, .pos a => .pos a
  | _, _, _, .neg a => .neg a
  | _, _, _, .bot => .bot
  | _, _, _, .top => .top
  | _, _, σ, .var i => σ i
  | _, _, σ, .conj p q => .conj (p.substitute σ) (q.substitute σ)
  | _, _, σ, .disj p q => .disj (p.substitute σ) (q.substitute σ)
  | _, _, σ, .box a p => .box a (p.substitute σ)
  | _, _, σ, .diamond a p => .diamond a (p.substitute σ)
  | _, _, σ, .mu p => .mu (p.substitute (liftSubstitution σ))
  | _, _, σ, .nu p => .nu (p.substitute (liftSubstitution σ))

end Silmaril.Logic.ModalMu
