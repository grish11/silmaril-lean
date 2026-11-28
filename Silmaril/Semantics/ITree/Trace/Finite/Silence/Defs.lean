module

public import Silmaril.Semantics.ITree.Trace.Finite.Defs
public import Silmaril.Semantics.ITree.Trace.Silence.Defs
public import Mathlib.Logic.Relation

@[expose] public section

namespace Silmaril.Elgot.ITree.Finite

universe u

variable {Q : Type} {R S : Type u} [DecidableEq S] [DecidableEq Q]

/-- A transition that takes no visible request and produces no return. -/
def SilentEdge (step : S → Step Q R S) (source target : S) : Prop :=
  step source = .inr target

/-- Follow a path of completed exchanges. Normalize silent control before
each exchange and at the endpoint. An unavailable exchange cannot witness
a silent endpoint. -/
def silentAfter? (step : S → Step Q R S) (states : Finset S) :
    S → ExchangePath (Event Q) → Bool
  | state, .nil =>
    match headFrom step states state with
    | .stop => true
    | _ => false
  | state, .cons (.ask key) reply tail =>
    match headFrom step states state with
    | .request actual next => if actual = key then silentAfter? step states (next reply) tail else false
    | _ => false

end Silmaril.Elgot.ITree.Finite
