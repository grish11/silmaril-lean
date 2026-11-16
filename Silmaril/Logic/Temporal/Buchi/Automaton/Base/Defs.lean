module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Symbolic
public import Silmaril.Logic.ModalMu.FiniteVector.Thms

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.Buchi.Automaton.Base
open ModalMu

/-- Finite disjunction as actual syntax, including the empty family. -/
def disjoin {S : Signature} {k : Nat} : {n : Nat} → (Fin n → Formula S k) → Formula S k
  | 0, _ => .bot
  | n+1, p => .disj (p 0) (disjoin (fun i : Fin n => p i.succ))

/-- Read guards at the source world, then take one edge of the original model. -/
def next {S : Signature} {n k : Nat} (A : Symbolic S.Atom n) (a : S.Action)
    (X : Fin n → Formula S k) (q : Fin n) : Formula S k :=
  disjoin (fun r => .conj (A.guard q r).toFormula (.diamond a (X r)))

/-- Inner least block: equation variables Y precede captured outer variables Z. -/
def innerSystem {S : Signature} {n : Nat} (A : Symbolic S.Atom n) (a : S.Action) :
    FiniteVector.System S n n where
  body q := .disj
    (if q ∈ A.accepting then next A a (fun r => .var (Fin.natAdd n r)) q else .bot)
    (next A a (fun r => .var (Fin.castAdd n r)) q)

/-- The compiled inner μ bodies form the outer simultaneous ν equations. -/
def outerSystem {S : Signature} {n : Nat} (A : Symbolic S.Atom n) (a : S.Action) :
    FiniteVector.System S n 0 where
  body q := (innerSystem A a).compile false q

/-- Actual closed scalar formulas evaluated on the original base model. -/
def coordinate {S : Signature} {n : Nat} (A : Symbolic S.Atom n) (a : S.Action)
    (q : Fin n) : Formula S 0 :=
  (outerSystem A a).compile true q

/-- Existential choice among initial automaton states, again as finite syntax. -/
def formula {S : Signature} {n : Nat} (A : Symbolic S.Atom n) (a : S.Action) :
    Formula S 0 :=
  disjoin (fun q => if q ∈ A.initial then coordinate A a q else .bot)

/-- Repackage a vector of world sets as a set of synchronized world/state pairs. -/
def productSets (W : Type) (n : Nat) : Env W n ≃o Set (W × Fin n) where
  toFun X := {x | x.1 ∈ X x.2}
  invFun P q := {w | (w, q) ∈ P}
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro X Y
    constructor
    · intro h q w hw
      exact h (show (w, q) ∈ {x | x.1 ∈ X x.2} from hw)
    · intro h x hx
      exact h x.2 hx

end Silmaril.Logic.Temporal.Buchi.Automaton.Base
