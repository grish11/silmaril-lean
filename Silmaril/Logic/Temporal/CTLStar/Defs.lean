module

public import Silmaril.Logic.CTL.Derived.Thms
public import Silmaril.Logic.Temporal.LTL.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar
open CategoryTheory Silmaril.Logic.Institution

abbrev Signature := CTL.Signature
/-- The discrete model category is required by the reduct to the existing CTL room.
Nontrivial frame isomorphisms are treated separately, without claiming discreteness
is necessary for CTL* semantics. -/
abbrev Model := CTL.Model

def ValidIndex (last : Option Nat) (i : Nat) : Prop :=
  match last with | none => True | some n => i ≤ n

/-- A maximal actual path. Padding after a finite last index is not a transition. -/
structure Path {W : Type} (R : W → W → Prop) where
  state : Nat → W
  last : Option Nat
  edges : ∀ i, ValidIndex last (i+1) →
    R (state i) (state (i+1))
  terminal : ∀ n, last = some n → ∀ v, ¬ R (state n) v

def Path.Valid {W : Type} {R : W → W → Prop} (p : Path R) (i : Nat) : Prop :=
  ValidIndex p.last i

mutual
inductive StateFormula (S : Signature)
  | atom : S.Atom → StateFormula S
  | bot : StateFormula S
  | neg : StateFormula S → StateFormula S
  | conj : StateFormula S → StateFormula S → StateFormula S
  | existsPath : PathFormula S → StateFormula S
inductive PathFormula (S : Signature)
  | state : StateFormula S → PathFormula S
  | neg : PathFormula S → PathFormula S
  | conj : PathFormula S → PathFormula S → PathFormula S
  | next : PathFormula S → PathFormula S
  | until : PathFormula S → PathFormula S → PathFormula S
end

mutual
def StateFormula.Holds {S : Signature} (M : Model S) :
    StateFormula S → M.toModal.World → Prop
  | .atom a, w => M.toModal.valuation a w
  | .bot, _ => False
  | .neg p, w => ¬ p.Holds M w
  | .conj p q, w => p.Holds M w ∧ q.Holds M w
  | .existsPath p, w => ∃ path : Path M.toModal.accessible,
      path.state 0 = w ∧ p.Holds M path 0
def PathFormula.Holds {S : Signature} (M : Model S) :
    PathFormula S → Path M.toModal.accessible → Nat → Prop
  | .state p, path, i => p.Holds M (path.state i)
  | .neg p, path, i => ¬ p.Holds M path i
  | .conj p q, path, i => p.Holds M path i ∧ q.Holds M path i
  | .next p, path, i => path.Valid (i+1) ∧ p.Holds M path (i+1)
  | .until p q, path, i => ∃ d, path.Valid (i+d) ∧ q.Holds M path (i+d) ∧
      ∀ j, j < d → p.Holds M path (i+j)
end

mutual
def StateFormula.map {S T : Signature} (f : S ⟶ T) : StateFormula S → StateFormula T
  | .atom a => .atom (f a)
  | .bot => .bot
  | .neg p => .neg (p.map f)
  | .conj p q => .conj (p.map f) (q.map f)
  | .existsPath p => .existsPath (p.map f)
def PathFormula.map {S T : Signature} (f : S ⟶ T) : PathFormula S → PathFormula T
  | .state p => .state (p.map f)
  | .neg p => .neg (p.map f)
  | .conj p q => .conj (p.map f) (q.map f)
  | .next p => .next (p.map f)
  | .until p q => .until (p.map f) (q.map f)
end

def StateFormula.top {S : Signature} : StateFormula S := .neg .bot
def StateFormula.allPaths {S : Signature} (p : PathFormula S) : StateFormula S :=
  .neg (.existsPath (.neg p))
def PathFormula.top {S : Signature} : PathFormula S := .state .top
def PathFormula.eventually {S : Signature} (p : PathFormula S) : PathFormula S :=
  .until .top p
def PathFormula.globally {S : Signature} (p : PathFormula S) : PathFormula S :=
  .neg (.eventually (.neg p))
/-- Exactly the infinite paths: strong next is available at every valid position. -/
def PathFormula.infinite {S : Signature} : PathFormula S := .globally (.next .top)

def Sat {S : Signature} (M : Model S) (p : StateFormula S) : Prop :=
  p.Holds M M.toModal.point

/-- Existing CTL's EG needs an infinite witness even on a nonserial frame. -/
def encodeCTL {S : Signature} : CTL.Formula S → StateFormula S
  | .atom a => .atom a
  | .bot => .bot
  | .neg p => .neg (encodeCTL p)
  | .conj p q => .conj (encodeCTL p) (encodeCTL q)
  | .ex p => .existsPath (.next (.state (encodeCTL p)))
  | .eu p q => .existsPath (.until (.state (encodeCTL p)) (.state (encodeCTL q)))
  | .eg p => .existsPath (.conj (.globally (.state (encodeCTL p))) .infinite)

/-- LTL enters path syntax, with no implicit state-level path quantifier. -/
def encodeLTL {S : Signature} : LTL.Formula S.Atom → PathFormula S
  | .atom a => .state (.atom a)
  | .bot => .state .bot
  | .not p => .neg (encodeLTL p)
  | .imp p q => .neg (.conj (encodeLTL p) (.neg (encodeLTL q)))
  | .and p q => .conj (encodeLTL p) (encodeLTL q)
  | .or p q => .neg (.conj (.neg (encodeLTL p)) (.neg (encodeLTL q)))
  | .next p => .next (encodeLTL p)
  | .until p q => .until (encodeLTL p) (encodeLTL q)

end Silmaril.Logic.Temporal.CTLStar
