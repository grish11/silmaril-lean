module

public import Silmaril.Logic.Temporal.LTL.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.LTL.NNF

/-- Positive temporal syntax. Only atomic predicates may be negated. -/
inductive Formula (Atom : Type) where
  | pos : Atom → Formula Atom
  | neg : Atom → Formula Atom
  | bot : Formula Atom
  | top : Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | next : Formula Atom → Formula Atom
  | until : Formula Atom → Formula Atom → Formula Atom
  | release : Formula Atom → Formula Atom → Formula Atom

/-- Direct infinite-word semantics. Until requires a finite witness. Release
requires q at every time up to and including the first possible p witness. -/
def Formula.Holds {Atom : Type} (word : Nat → Atom → Prop) : Formula Atom → Nat → Prop
  | .pos a, n => word n a
  | .neg a, n => ¬ word n a
  | .bot, _ => False
  | .top, _ => True
  | .conj p q, n => p.Holds word n ∧ q.Holds word n
  | .disj p q, n => p.Holds word n ∨ q.Holds word n
  | .next p, n => p.Holds word (n+1)
  | .until p q, n => ∃ d, q.Holds word (n+d) ∧
      ∀ i, i < d → p.Holds word (n+i)
  | .release p q, n => ∀ d, q.Holds word (n+d) ∨
      ∃ i, i < d ∧ p.Holds word (n+i)

def Formula.map {Atom Atom' : Type} (f : Atom → Atom') : Formula Atom → Formula Atom'
  | .pos a => .pos (f a)
  | .neg a => .neg (f a)
  | .bot => .bot
  | .top => .top
  | .conj p q => .conj (p.map f) (q.map f)
  | .disj p q => .disj (p.map f) (q.map f)
  | .next p => .next (p.map f)
  | .until p q => .until (p.map f) (q.map f)
  | .release p q => .release (p.map f) (q.map f)

/-- Syntactic temporal dual, without an arbitrary negation constructor. -/
def Formula.dual {Atom : Type} : Formula Atom → Formula Atom
  | .pos a => .neg a
  | .neg a => .pos a
  | .bot => .top
  | .top => .bot
  | .conj p q => .disj p.dual q.dual
  | .disj p q => .conj p.dual q.dual
  | .next p => .next p.dual
  | .until p q => .release p.dual q.dual
  | .release p q => .until p.dual q.dual

/-- false preserves truth; true normalizes the negation. All input temporal
nesting and arbitrary negations are handled structurally. -/
def normalize {Atom : Type} : Bool → LTL.Formula Atom → Formula Atom
  | b, .atom a => if b then .neg a else .pos a
  | b, .bot => if b then .top else .bot
  | b, .not p => normalize (!b) p
  | false, .imp p q => .disj (normalize true p) (normalize false q)
  | true, .imp p q => .conj (normalize false p) (normalize true q)
  | false, .and p q => .conj (normalize false p) (normalize false q)
  | true, .and p q => .disj (normalize true p) (normalize true q)
  | false, .or p q => .disj (normalize false p) (normalize false q)
  | true, .or p q => .conj (normalize true p) (normalize true q)
  | b, .next p => .next (normalize b p)
  | false, .until p q => .until (normalize false p) (normalize false q)
  | true, .until p q => .release (normalize true p) (normalize true q)

end Silmaril.Logic.Temporal.LTL.NNF
