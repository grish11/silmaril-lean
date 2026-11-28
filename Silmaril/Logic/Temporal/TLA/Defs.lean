module

/-!
# Simple TLA over typed states

The temporal constructors follow Fig. 4 of Lamport's *The Temporal Logic
of Actions*. State expressions and actions are given by their denotations
in Lean. See `docs/projects/tla.md` for the fragments and semantic contracts.
-/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA

universe u v

variable {S : Type u} {V : Type v}

/-- An infinite behavior with one state at each natural-number time. -/
abbrev Behavior (S : Type u) := Nat → S

abbrev StateExpr (S : Type u) (V : Type v) := S → V
abbrev StatePred (S : Type u) := S → Prop
abbrev Action (S : Type u) := S → S → Prop

namespace Behavior

def suffix (σ : Behavior S) (n : Nat) : Behavior S := fun i => σ (n + i)

def map (f : S → V) (σ : Behavior S) : Behavior V := fun i => f (σ i)

end Behavior

namespace Action

/-- Interpret a state expression at the source of a step. -/
def current (f : StateExpr S V) (s _ : S) : V := f s

/-- Interpret a primed state expression at the target of a step. -/
def prime (f : StateExpr S V) (_ t : S) : V := f t

/-- The action admits some successor in the state space. -/
def enabled (A : Action S) : StatePred S := fun s => ∃ t, A s t

def unchanged (f : StateExpr S V) : Action S := fun s t => prime f s t = current f s t

/-- The bracket action `[A]_f`. -/
def bracket (A : Action S) (f : StateExpr S V) : Action S :=
  fun s t => A s t ∨ unchanged f s t

/-- The angle action `⟨A⟩_f`. -/
def angle (A : Action S) (f : StateExpr S V) : Action S :=
  fun s t => A s t ∧ ¬ unchanged f s t

end Action

/-- Repeat each time instant a positive finite number of times. Starting at zero
and advancing by at most one ensures every original step has a corresponding
step. Cofinality rules out stopping forever before a future step. -/
structure Retiming where
  index : Nat → Nat
  zero : index 0 = 0
  step (i : Nat) : index (i + 1) = index i ∨ index (i + 1) = index i + 1
  cofinal (j : Nat) : ∃ i, j ≤ index i

def Behavior.retime (σ : Behavior S) (r : Retiming) : Behavior S := fun i => σ (r.index i)

/-- Two behaviors have a common expansion by repeating whole states. -/
def StutterEquiv (σ τ : Behavior S) : Prop :=
  ∃ r t : Retiming, σ.retime r = τ.retime t

/-- A predicate gives the same answer on stuttering-equivalent behaviors. -/
def StutterInvariant (p : Behavior S → Prop) : Prop :=
  ∀ ⦃σ τ⦄, StutterEquiv σ τ → (p σ ↔ p τ)

/-- Flexible hiding for split states. A witness has its own hidden component
at every instant and agrees with the visible behavior up to stuttering. -/
def hide (p : Behavior (S × V) → Prop) (σ : Behavior S) : Prop :=
  ∃ τ, StutterEquiv σ (τ.map Prod.fst) ∧ p τ

/-- Temporal syntax with denotational state predicates and actions as leaves.
The bracket modality is primitive. A bare action is not a formula. -/
inductive Formula : Type u → Type (u + 1) where
  | state {S : Type u} (p : StatePred S) : Formula S
  | alwaysBracket {S V : Type u} (A : Action S) (f : StateExpr S V) : Formula S
  | neg {S : Type u} (p : Formula S) : Formula S
  | conj {S : Type u} (p q : Formula S) : Formula S
  | always {S : Type u} (p : Formula S) : Formula S
  /-- Choose one value for the entire formula body. -/
  | existsRigid {S V : Type u} (p : V → Formula S) : Formula S
  /-- Extend the state at every instant, then hide the new coordinate. -/
  | existsFlex {S V : Type u} (p : Formula (S × V)) : Formula S

namespace Formula

def Holds : {S : Type u} → Behavior S → Formula S → Nat → Prop
  | _, σ, .state p, n => p (σ n)
  | _, σ, .alwaysBracket A f, n => ∀ j, n ≤ j → A.bracket f (σ j) (σ (j + 1))
  | _, σ, .neg p, n => ¬ p.Holds σ n
  | _, σ, .conj p q, n => p.Holds σ n ∧ q.Holds σ n
  | _, σ, .always p, n => ∀ j, n ≤ j → p.Holds σ j
  | _, σ, .existsRigid p, n => ∃ v, (p v).Holds σ n
  | _, σ, .existsFlex p, n => hide (fun τ => p.Holds τ 0) (σ.suffix n)

def Sat (p : Formula S) (σ : Behavior S) : Prop := p.Holds σ 0

def Entails (p q : Formula S) : Prop := ∀ σ, p.Sat σ → q.Sat σ

def disj (p q : Formula S) : Formula S := .neg (.conj (.neg p) (.neg q))

def imp (p q : Formula S) : Formula S := .neg (.conj p (.neg q))
def forallRigid {V : Type u} (p : V → Formula S) : Formula S := .neg (.existsRigid fun v => .neg (p v))

def forallFlex {V : Type u} (p : Formula (S × V)) : Formula S := .neg (.existsFlex (.neg p))

def eventually (p : Formula S) : Formula S := .neg (.always (.neg p))

def eventuallyAngle {V : Type u} (A : Action S) (f : StateExpr S V) : Formula S :=
  .neg (.alwaysBracket (fun s t => ¬ A s t) f)

def leadsTo (p q : Formula S) : Formula S := .always (imp p (eventually q))

/-- `WF_f(A)`: repeatedly take an angle step or repeatedly be disabled. -/
def weakFair {V : Type u} (A : Action S) (f : StateExpr S V) : Formula S :=
  let disabled := Formula.state fun s => ¬ (A.angle f).enabled s
  disj (.always (eventuallyAngle A f)) (.always (eventually disabled))

/-- `SF_f(A)`: repeatedly take an angle step or eventually stay disabled. -/
def strongFair {V : Type u} (A : Action S) (f : StateExpr S V) : Formula S :=
  let disabled := Formula.state fun s => ¬ (A.angle f).enabled s
  disj (.always (eventuallyAngle A f)) (eventually (.always disabled))

/-- The usual `Init ∧ □[Next]_f ∧ Live` shape. Supply a conjunction of fairness clauses
for `Live`, or the constantly true state predicate for a safety-only spec. -/
def spec {V : Type u} (init : StatePred S) (next : Action S) (f : StateExpr S V)
    (live : Formula S) : Formula S :=
  .conj (.state init) (.conj (.alwaysBracket next f) live)

end Formula

end Silmaril.Logic.Temporal.TLA
