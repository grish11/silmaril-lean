module

public import Silmaril.Logic.Temporal.TLA.General.Defs

/-! # Integer and Boolean semantics for scoped TLA

Terms are denotations with typed inputs. Predicates pair a proposition with
a computable decision procedure. State terms use a single flexible valuation,
and step terms use an ordered source and target pair.
-/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Kernel

inductive Scalar where
  | int
  | bool
  deriving DecidableEq

/-- Fixed carriers for the kernel's scalar fragment. -/
def Value : Scalar → Type
  | .int => Int
  | .bool => Bool

instance (a : Scalar) : DecidableEq (Value a) :=
  match a with
  | .int => inferInstanceAs (DecidableEq Int)
  | .bool => inferInstanceAs (DecidableEq Bool)

abbrev Scope := General.Scope Scalar
abbrev RigidEnv (Γ : Scope) := General.RigidEnv Value Γ
abbrev State (Γ : Scope) := General.State Value Γ

/-- A denotation over a rigid environment and a caller-selected input.
The state and step interfaces use the inputs in `StateExpr` and `StepExpr`. -/
abbrev Term (Γ : Scope) (Input X : Type) := RigidEnv Γ → Input → X

/-- Definitionally the General TLA expression type at these fixed carriers. -/
abbrev StateExpr (Γ : Scope) (X : Type) := Term Γ (State Γ) X
abbrev StepExpr (Γ : Scope) (X : Type) := Term Γ (State Γ × State Γ) X

/-- The decision procedure is indexed by the proposition it decides. -/
structure Predicate (Γ : Scope) (Input : Type) where
  holds : Term Γ Input Prop
  decision (ρ : RigidEnv Γ) (input : Input) : Decidable (holds ρ input)

abbrev StatePredicate (Γ : Scope) := Predicate Γ (State Γ)
abbrev StepPredicate (Γ : Scope) := Predicate Γ (State Γ × State Γ)

variable {Γ : Scope} {Input X Y Z : Type}

namespace Term

def literal (value : X) : Term Γ Input X := fun _ _ => value

def rigid {a : Scalar} (name : Γ.rigid a) : Term Γ Input (Value a) :=
  fun ρ _ => ρ a name

def flex {a : Scalar} (name : Γ.flex a) : StateExpr Γ (Value a) :=
  General.Expr.flex name

def map (f : X → Y) (e : Term Γ Input X) : Term Γ Input Y :=
  fun ρ input => f (e ρ input)

def map₂ (f : X → Y → Z) (left : Term Γ Input X) (right : Term Γ Input Y) : Term Γ Input Z :=
  fun ρ input => f (left ρ input) (right ρ input)

def enumeration (elements : List (Term Γ Input X)) : Term Γ Input (List X) :=
  fun ρ input => elements.map fun e => e ρ input

def current (e : StateExpr Γ X) : StepExpr Γ X :=
  fun ρ (s, t) => TLA.Action.current (e ρ) s t

def next (e : StateExpr Γ X) : StepExpr Γ X :=
  fun ρ (s, t) => TLA.Action.prime (e ρ) s t

def weakenRigid (e : Term Γ Input X) (a : Scalar) : Term (Γ.bindRigid a) Input X :=
  fun ρ input => e ρ.drop input

def neg (e : Term Γ Input Int) : Term Γ Input Int := e.map (fun x => -x)
def add (e f : Term Γ Input Int) : Term Γ Input Int := map₂ (· + ·) e f
def sub (e f : Term Γ Input Int) : Term Γ Input Int := map₂ (· - ·) e f
def mul (e f : Term Γ Input Int) : Term Γ Input Int := map₂ (· * ·) e f

def ite (condition : Predicate Γ Input) (yes no : Term Γ Input X) : Term Γ Input X :=
  fun ρ input => @_root_.ite _ (condition.holds ρ input) (condition.decision ρ input)
    (yes ρ input) (no ρ input)

end Term

namespace Predicate

/-- Run the decision procedure as a Boolean term. -/
def check (p : Predicate Γ Input) : Term Γ Input Bool :=
  fun ρ input => @decide (p.holds ρ input) (p.decision ρ input)

/-- Lift a pointwise decidable relation on term values. -/
def compare (rel : X → Y → Prop) [decision : ∀ x y, Decidable (rel x y)]
    (e : Term Γ Input X) (f : Term Γ Input Y) : Predicate Γ Input where
  holds := Term.map₂ rel e f
  decision ρ input := decision (e ρ input) (f ρ input)

def eq [DecidableEq X] (e f : Term Γ Input X) : Predicate Γ Input := compare Eq e f
def lt (e f : Term Γ Input Int) : Predicate Γ Input := compare (· < ·) e f
def le (e f : Term Γ Input Int) : Predicate Γ Input := compare (· ≤ ·) e f

def ofBool (e : Term Γ Input Bool) : Predicate Γ Input := eq e (Term.literal true)

def not (p : Predicate Γ Input) : Predicate Γ Input where
  holds ρ input := ¬ p.holds ρ input
  decision ρ input :=
    letI := p.decision ρ input
    inferInstance

def and (p q : Predicate Γ Input) : Predicate Γ Input where
  holds ρ input := p.holds ρ input ∧ q.holds ρ input
  decision ρ input :=
    letI := p.decision ρ input
    letI := q.decision ρ input
    inferInstance

def or (p q : Predicate Γ Input) : Predicate Γ Input where
  holds ρ input := p.holds ρ input ∨ q.holds ρ input
  decision ρ input :=
    letI := p.decision ρ input
    letI := q.decision ρ input
    inferInstance

def implies (p q : Predicate Γ Input) : Predicate Γ Input where
  holds ρ input := p.holds ρ input → q.holds ρ input
  decision ρ input :=
    letI := p.decision ρ input
    letI := q.decision ρ input
    inferInstance

def iff (p q : Predicate Γ Input) : Predicate Γ Input where
  holds ρ input := p.holds ρ input ↔ q.holds ρ input
  decision ρ input :=
    letI := p.decision ρ input
    letI := q.decision ρ input
    inferInstance

def current (p : StatePredicate Γ) : StepPredicate Γ where
  holds := Term.current p.holds
  decision ρ input := p.decision ρ input.1

def next (p : StatePredicate Γ) : StepPredicate Γ where
  holds := Term.next p.holds
  decision ρ input := p.decision ρ input.2

def weakenRigid (p : Predicate Γ Input) (a : Scalar) : Predicate (Γ.bindRigid a) Input where
  holds := p.holds.weakenRigid a
  decision ρ input := p.decision ρ.drop input

/-- Evaluate the domain in the outer environment. Each witness extends the same
rigid valuation for the entire body, including both ends of a step. -/
def existsIn {a : Scalar} (domain : Term Γ Input (List (Value a)))
    (body : Predicate (Γ.bindRigid a) Input) : Predicate Γ Input where
  holds ρ input := ∃ value ∈ domain ρ input, body.holds (ρ.extend value) input
  decision ρ input :=
    letI : DecidablePred (fun value => body.holds (ρ.extend value) input) :=
      fun value => body.decision (ρ.extend value) input
    List.decidableBEx _ (domain ρ input)

def forallIn {a : Scalar} (domain : Term Γ Input (List (Value a)))
    (body : Predicate (Γ.bindRigid a) Input) : Predicate Γ Input where
  holds ρ input := ∀ value ∈ domain ρ input, body.holds (ρ.extend value) input
  decision ρ input :=
    letI : DecidablePred (fun value => body.holds (ρ.extend value) input) :=
      fun value => body.decision (ρ.extend value) input
    List.decidableBAll _ (domain ρ input)

def toStatePred (p : StatePredicate Γ) : General.StatePred Value Γ := .atom p.holds

/-- Interpret a predicate on one fixed pair of valuations. A constraint on a
next coordinate leaves any other coordinates free unless separately constrained. -/
def toAction (p : StepPredicate Γ) : General.Action Value Γ :=
  fun ρ s t => p.holds ρ (s, t)

/-- Explicitly add steps whose observation is unchanged. -/
def bracket [DecidableEq X] (p : StepPredicate Γ) (observe : StateExpr Γ X) : StepPredicate Γ :=
  p.or (Predicate.eq (Term.next observe) (Term.current observe))

end Predicate

/-- Explicit state candidates and their valuations. Repeated candidates in
the list can yield repeated results. -/
structure Bounded (Γ : Scope) (Node : Type) where
  states : List Node
  valuation : Node → State Γ

namespace Bounded

variable {Node : Type}

def initials (domain : Bounded Γ Node) (ρ : RigidEnv Γ) (init : StatePredicate Γ) : List Node :=
  domain.states.filter fun node => init.check ρ (domain.valuation node)

/-- Enumerate accepted pairs from the same given domain on both ends. Pass the
raw predicate for its transition relation. -/
def transitions (domain : Bounded Γ Node) (ρ : RigidEnv Γ) (step : StepPredicate Γ) :
    List (Node × Node) :=
  domain.states.flatMap fun src =>
    let source := domain.valuation src
    let targets := domain.states.filter fun dst => step.check ρ (source, domain.valuation dst)
    targets.map fun dst => (src, dst)

end Bounded

end Silmaril.Logic.Temporal.TLA.Kernel
