module

public import Silmaril.Logic.Temporal.CTLStar.Terminal.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.NNF

/-- Positive path syntax for finite endpoints as well as infinite paths.
Only leaves are negated; strong and weak next are distinct constructors. -/
inductive Formula (Atom : Type) where
  | pos : Atom → Formula Atom
  | neg : Atom → Formula Atom
  | bot : Formula Atom
  | top : Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | strongNext : Formula Atom → Formula Atom
  | weakNext : Formula Atom → Formula Atom
  | until : Formula Atom → Formula Atom → Formula Atom
  | release : Formula Atom → Formula Atom → Formula Atom

/-- Direct bounded-word semantics. A finite last position is included.
Only valid starting positions are used by the CTL* correspondence theorems. -/
def Formula.Holds {Atom : Type} (last : Option Nat) (word : Nat → Atom → Prop) :
    Formula Atom → Nat → Prop
  | .pos a, i => word i a
  | .neg a, i => ¬ word i a
  | .bot, _ => False
  | .top, _ => True
  | .conj p q, i => p.Holds last word i ∧ q.Holds last word i
  | .disj p q, i => p.Holds last word i ∨ q.Holds last word i
  | .strongNext p, i => ValidIndex last (i+1) ∧ p.Holds last word (i+1)
  | .weakNext p, i => ValidIndex last (i+1) → p.Holds last word (i+1)
  | .until p q, i => ∃ d, ValidIndex last (i+d) ∧ q.Holds last word (i+d) ∧
      ∀ j, j < d → p.Holds last word (i+j)
  | .release p q, i => ∀ d, ValidIndex last (i+d) → q.Holds last word (i+d) ∨
      ∃ j, j < d ∧ p.Holds last word (i+j)

def Formula.map {A B : Type} (f : A → B) : Formula A → Formula B
  | .pos a => .pos (f a)
  | .neg a => .neg (f a)
  | .bot => .bot
  | .top => .top
  | .conj p q => .conj (p.map f) (q.map f)
  | .disj p q => .disj (p.map f) (q.map f)
  | .strongNext p => .strongNext (p.map f)
  | .weakNext p => .weakNext (p.map f)
  | .until p q => .until (p.map f) (q.map f)
  | .release p q => .release (p.map f) (q.map f)

/-- Temporal dual swaps strong/weak next and until/release. -/
def Formula.dual {A : Type} : Formula A → Formula A
  | .pos a => .neg a
  | .neg a => .pos a
  | .bot => .top
  | .top => .bot
  | .conj p q => .disj p.dual q.dual
  | .disj p q => .conj p.dual q.dual
  | .strongNext p => .weakNext p.dual
  | .weakNext p => .strongNext p.dual
  | .until p q => .release p.dual q.dual
  | .release p q => .until p.dual q.dual

/-- Interpret leaves by actual CTL* state formulas; temporal operators keep one path. -/
def Formula.toPathFormula {A : Type} {S : Signature} (leaf : A → StateFormula S) :
    Formula A → PathFormula S
  | .pos a => .state (leaf a)
  | .neg a => .neg (.state (leaf a))
  | .bot => .state .bot
  | .top => .top
  | .conj p q => .conj (p.toPathFormula leaf) (q.toPathFormula leaf)
  | .disj p q => .neg (.conj (.neg (p.toPathFormula leaf)) (.neg (q.toPathFormula leaf)))
  | .strongNext p => .next (p.toPathFormula leaf)
  | .weakNext p => (p.toPathFormula leaf).weakNext
  | .until p q => .until (p.toPathFormula leaf) (q.toPathFormula leaf)
  | .release p q => (p.toPathFormula leaf).release (q.toPathFormula leaf)

/-- Normalize path-level negations; embedded state formulas remain whole leaves.
false preserves truth and true normalizes the complement. -/
def normalize {S : Signature} : Bool → PathFormula S → Formula (StateFormula S)
  | b, .state p => if b then .neg p else .pos p
  | b, .neg p => normalize (!b) p
  | false, .conj p q => .conj (normalize false p) (normalize false q)
  | true, .conj p q => .disj (normalize true p) (normalize true q)
  | false, .next p => .strongNext (normalize false p)
  | true, .next p => .weakNext (normalize true p)
  | false, .until p q => .until (normalize false p) (normalize false q)
  | true, .until p q => .release (normalize true p) (normalize true q)

end Silmaril.Logic.Temporal.CTLStar.NNF
