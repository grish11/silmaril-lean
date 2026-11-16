module

public import Silmaril.Logic.Temporal.Buchi.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.Buchi

/-- A nondeterministic word automaton with exactly n states. Zero states are
allowed. No determinism, totality or decidability of transitions is assumed. -/
structure Automaton (Letter : Type) (n : Nat) where
  initial : Set (Fin n)
  step : Fin n → Letter → Fin n → Prop
  accepting : Set (Fin n)

namespace Automaton
variable {Letter NewLetter W : Type} {n : Nat}

abbrev Word (Letter : Type) := Nat → Letter

/-- The letter at time k is consumed by the transition from r k to r (k+1). -/
def IsRun (A : Automaton Letter n) (word : Word Letter) (r : Nat → Fin n) : Prop :=
  ∀ k, A.step (r k) (word k) (r (k+1))

/-- Infinitely many visits on this one run, including time zero when applicable. -/
def Recurrent (A : Automaton Letter n) (r : Nat → Fin n) : Prop :=
  ∀ k, ∃ m, k ≤ m ∧ r m ∈ A.accepting

def AcceptsFrom (A : Automaton Letter n) (word : Word Letter) (q : Fin n) : Prop :=
  ∃ r, r 0 = q ∧ A.IsRun word r ∧ A.Recurrent r

/-- Acceptance independently quantifies one infinite automaton run. -/
def Accepts (A : Automaton Letter n) (word : Word Letter) : Prop :=
  ∃ r, r 0 ∈ A.initial ∧ A.IsRun word r ∧ A.Recurrent r

/-- One infinite graph path, without imposing seriality on other states. -/
def IsPath (R : W → W → Prop) (w : W) (p : Nat → W) : Prop :=
  p 0 = w ∧ ∀ k, R (p k) (p (k+1))

/-- One graph path and one accepting run on its actual label word. -/
def AcceptsPath (A : Automaton Letter n) (R : W → W → Prop)
    (label : W → Letter) (w : W) : Prop :=
  ∃ p, IsPath R w p ∧ A.Accepts (label ∘ p)

/-- Synchronous product. Consume the source world's label, then advance both
coordinates. Neither successor nor automaton choice is selected in advance. -/
def productStep (A : Automaton Letter n) (R : W → W → Prop)
    (label : W → Letter) (x y : W × Fin n) : Prop :=
  R x.1 y.1 ∧ A.step x.2 (label x.1) y.2

def productAccepting (A : Automaton Letter n) : Set (W × Fin n) :=
  {x | x.2 ∈ A.accepting}

/-- Pull back the alphabet; states and nondeterministic choices are unchanged. -/
def comap (A : Automaton Letter n) (f : NewLetter → Letter) : Automaton NewLetter n where
  initial := A.initial
  step q a r := A.step q (f a) r
  accepting := A.accepting

end Automaton
end Silmaril.Logic.Temporal.Buchi
