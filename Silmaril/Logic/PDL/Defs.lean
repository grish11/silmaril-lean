module

public import Silmaril.Logic.ModalMu.Variables.Thms
public import Mathlib.Logic.Relation

@[expose] public section
namespace Silmaril.Logic.PDL
open CategoryTheory

abbrev Signature := ModalMu.Signature
abbrev Model := ModalMu.Model

mutual
  inductive Formula (S : Signature) where
    | atom : S.Atom → Formula S
    | bot : Formula S
    | neg : Formula S → Formula S
    | conj : Formula S → Formula S → Formula S
    | disj : Formula S → Formula S → Formula S
    | box : Program S → Formula S → Formula S
    | diamond : Program S → Formula S → Formula S

  inductive Program (S : Signature) where
    | action : S.Action → Program S
    | seq : Program S → Program S → Program S
    | choice : Program S → Program S → Program S
    | star : Program S → Program S
    | test : Formula S → Program S
end

mutual
  def Formula.map {S T : Signature} (f : S ⟶ T) : Formula S → Formula T
    | .atom a => .atom (f.atom a)
    | .bot => .bot
    | .neg p => .neg (p.map f)
    | .conj p q => .conj (p.map f) (q.map f)
    | .disj p q => .disj (p.map f) (q.map f)
    | .box a p => .box (a.map f) (p.map f)
    | .diamond a p => .diamond (a.map f) (p.map f)

  def Program.map {S T : Signature} (f : S ⟶ T) : Program S → Program T
    | .action a => .action (f.action a)
    | .seq a b => .seq (a.map f) (b.map f)
    | .choice a b => .choice (a.map f) (b.map f)
    | .star a => .star (a.map f)
    | .test p => .test (p.map f)
end

mutual
  def Formula.Holds {S : Signature} (M : Model S) : Formula S → M.World → Prop
    | .atom a, w => w ∈ M.valuation a
    | .bot, _ => False
    | .neg p, w => ¬ p.Holds M w
    | .conj p q, w => p.Holds M w ∧ q.Holds M w
    | .disj p q, w => p.Holds M w ∨ q.Holds M w
    | .box a p, w => ∀ v, a.Rel M w v → p.Holds M v
    | .diamond a p, w => ∃ v, a.Rel M w v ∧ p.Holds M v

  /-- Star is actual finite reflexive-transitive closure, not an uninterpreted relation. -/
  def Program.Rel {S : Signature} (M : Model S) : Program S → M.World → M.World → Prop
    | .action a, w, v => M.step a w v
    | .seq a b, w, v => ∃ u, a.Rel M w u ∧ b.Rel M u v
    | .choice a b, w, v => a.Rel M w v ∨ b.Rel M w v
    | .star a, w, v => Relation.ReflTransGen (a.Rel M) w v
    | .test p, w, v => w = v ∧ p.Holds M w
end

def Sat {S : Signature} (M : Model S) (p : Formula S) := p.Holds M M.point

/-- Explicit path length witnesses that star ranges only over finite executions. -/
inductive Steps {W : Type} (r : W → W → Prop) : Nat → W → W → Prop
  | zero (w : W) : Steps r 0 w w
  | tail {n w u v} : Steps r n w u → r u v → Steps r (n + 1) w v

end Silmaril.Logic.PDL
