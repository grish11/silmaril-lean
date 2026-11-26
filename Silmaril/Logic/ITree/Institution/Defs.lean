module

public import Silmaril.Logic.Institution.Basic
public import Silmaril.Semantics.ITree.Signature.Thms

/-! # An institution of handled interaction-tree return laws -/

@[expose] public section

namespace Silmaril.Logic.ITree

open CategoryTheory Silmaril.Elgot.ITree

universe u v w

variable {S T U : Signature.{u}} {E : Type u → Type u} {A : Type v} {X Y : Type w}

/-- A model gives a state space, a predicate of initial states, and a relational
handler. The model categories below are discrete: their equality is equality
of this data, and changes of state presentation are handled by explicit equivalences. -/
structure Model (S : Signature.{u}) where
  State : Type w
  initial : State → Prop
  step : Handler State S.Event

/-- Reduct preserves the initial states and projects each target reply through
the morphism's backward reply map. -/
def Model.reduct (f : S ⟶ T) (M : Model.{u,w} T) : Model.{u,w} S :=
  ⟨M.State, M.initial, f.restrict M.step⟩

/-- Push a handler and its initial predicate forward across a state equivalence. -/
def Model.renameState (M : Model S) (e : M.State ≃ X) : Model.{u,w} S where
  State := X
  initial x := M.initial (e.symm x)
  step q x r y := M.step q (e.symm x) r (e.symm y)

/-- Runs with exactly the specified number of completed exchanges followed by
a return of the specified value. A pending request contributes no such run. -/
def Runs (step : Handler X E) (a : A) :
    Nat → X → Tree E A → Prop
  | 0, _, t => out t = Part.some (.ret a)
  | n + 1, x, t =>
      ∃ node ∈ out t, match node with
        | .ret _ => False
        | .vis ev k => ∃ r y, step ⟨_, ev⟩ x r y ∧ Runs step a n y (k r)

/-- The trace has exactly the given number of exchanges and ends in this return. -/
def TraceReturns (a : A) : Nat → Trace E A → Prop
  | 0, .result b => b = a
  | n + 1, .exchange _ _ tail => TraceReturns a n tail
  | _, _ => False

/-- A sentence is a weak interaction tree and a predicate on its return values. -/
structure Sentence (S : Signature.{u}) where
  Result : Type v
  program : Tree S.Event Result
  post : Result → Prop

/-- Translate the program, keeping the same result type and predicate. -/
def Sentence.translate (f : S ⟶ T) (φ : Sentence.{u,v} S) : Sentence.{u,v} T :=
  ⟨φ.Result, f.tree id φ.program, φ.post⟩

/-- All admitted finite returns from every initial state satisfy the postcondition. -/
def Sat (M : Model.{u,w} S) (φ : Sentence.{u,v} S) : Prop :=
  ∀ x, M.initial x → ∀ n a, Runs M.step a n x φ.program → φ.post a

end Silmaril.Logic.ITree
