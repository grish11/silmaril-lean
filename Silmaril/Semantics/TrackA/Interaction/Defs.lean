module

public import Mathlib.Data.Set.Basic
public import Silmaril.Semantics.Operational.Execution

/-! # Delayed interaction and choice

The presentation is a coalgebra with an explicit state carrier. A root unfolds
by taking one layer at a time, and can support genuinely infinite executions.
The carrier is part of the presentation, so equality of presentations is
separate from the observation relation below.
-/

@[expose] public section

namespace Silmaril.Semantics.TrackA.Interaction
universe u v w x y z s b c t r i h

/-- Requests with dependent response types. Also used for choice shapes and
their branch indices. -/
structure Signature where
  Request : Type u
  Response : Request → Type v

namespace Signature

/-- A container morphism. The translated request is sent to the target, and
its response is decoded to choose a source continuation. -/
structure Hom (S : Signature.{u,v}) (T : Signature.{w,x}) where
  request : S.Request → T.Request
  response (q : S.Request) : T.Response (request q) → S.Response q

def Hom.id (S : Signature.{u,v}) : Hom S S := ⟨fun q => q, fun _ r => r⟩

def Hom.comp {S : Signature.{u,v}} {T : Signature.{w,x}} {U : Signature.{y,z}}
    (g : Hom T U) (f : Hom S T) : Hom S U :=
  ⟨fun q => g.request (f.request q), fun q r => f.response q (g.response (f.request q) r)⟩

/-- The type of completed exchanges, including the actual response. -/
abbrev Exchange (S : Signature.{u,v}) := Sigma S.Response

/-- No choice nodes are available in the deterministic fragment. -/
def noChoice : Signature.{0,0} := ⟨Empty, Empty.elim⟩

/-- Finite CTree choice with arbitrary arity, including deadlock at arity zero. -/
def finiteChoice : Signature.{0,0} := ⟨Nat, Fin⟩

end Signature

inductive ChoiceKind where
  | delayed
  | stepping

/-- One unfolding layer. Immediate failure and UB can be represented as
separate result constructors in `A`. -/
inductive Node (S : Signature.{u,v}) (B : Signature.{w,x}) (A : Type y) (X : Type z) where
  | ret (result : A)
  | tau (next : X)
  | vis (q : S.Request) (next : S.Response q → X)
  | branch (kind : ChoiceKind) (shape : B.Request) (next : B.Response shape → X)

def Node.relabel {S : Signature.{u,v}} {T : Signature.{w,x}} {B : Signature.{b,c}}
    {A : Type y} {X : Type z} (f : Signature.Hom S T) : Node S B A X → Node T B A X
  | .ret a => .ret a
  | .tau next => .tau next
  | .vis q next => .vis (f.request q) fun r => next (f.response q r)
  | .branch kind shape next => .branch kind shape next

abbrev Coalgebra (S : Signature.{u,v}) (B : Signature.{w,x}) (A : Type y) (X : Type z) :=
  X → Node S B A X

/-- A family of roots sharing a coalgebra. The root index can be empty. -/
structure Forest (S : Signature.{u,v}) (B : Signature.{w,x}) (A : Type y) (I : Type z) where
  State : Type s
  unfold : Coalgebra S B A State
  root : I → State

/-- A single rooted tree with arbitrary dependent choice. -/
abbrev ChoiceTree (S : Signature.{u,v}) (B : Signature.{w,x}) (A : Type y) :=
  Forest S B A Unit

abbrev CTree (S : Signature.{u,v}) (A : Type y) := ChoiceTree S Signature.finiteChoice A

abbrev ITree (S : Signature.{u,v}) (A : Type y) := ChoiceTree S Signature.noChoice A

namespace Coalgebra

variable {S : Signature.{u,v}} {B : Signature.{w,x}} {A : Type y} {X : Type z}

inductive Action (S : Signature.{u,v}) (B : Signature.{w,x}) where
  | tau
  | select (kind : ChoiceKind) (shape : B.Request) (index : B.Response shape)
  | exchange (event : S.Exchange)

/-- Each edge is justified by one unfolding of the source state. -/
inductive Step (c : Coalgebra S B A X) : X → Action S B → X → Prop where
  | tau {x y : X} : c x = .tau y → Step c x .tau y
  | choice {x : X} {kind : ChoiceKind} {shape : B.Request} {next : B.Response shape → X}
      (h : c x = .branch kind shape next) (i : B.Response shape) :
      Step c x (.select kind shape i) (next i)
  | vis {x : X} {q : S.Request} {next : S.Response q → X}
      (h : c x = .vis q next) (r : S.Response q) :
      Step c x (.exchange ⟨q, r⟩) (next r)

/-- In the weak observation policy both kinds of choice are internal. Their
edges, as well as tau, count towards divergence. -/
def Internal (c : Coalgebra S B A X) (x y : X) : Prop :=
  Step c x .tau y ∨ ∃ kind shape i, Step c x (.select kind shape i) y

def Silent (c : Coalgebra S B A X) := Relation.ReflTransGen (Internal c)

def WeakStep (c : Coalgebra S B A X) (x : X) (e : S.Exchange) (y : X) : Prop :=
  ∃ mid, Silent c x mid ∧ Step c mid (.exchange e) y

/-- Guarded feedback. Restarting from a recursive result takes a tau step. -/
def iterate {I : Type i} (c : Coalgebra S B (A ⊕ I) X) (entry : I → X) : Coalgebra S B A X :=
  fun x =>
    match c x with
    | .ret (.inl a) => .ret a
    | .ret (.inr i) => .tau (entry i)
    | .tau next => .tau next
    | .vis q next => .vis q next
    | .branch kind shape next => .branch kind shape next

/-- A stateful, total handler of one request at a time. Encoded errors are
ordinary replies, so the handler continues using the source response type. -/
abbrev Handler (S : Signature.{u,v}) (H : Type h) :=
  H → (q : S.Request) → S.Response q × H

/-- Handle each source request atomically in one tau step. Choices and existing
tau steps leave handler state unchanged. -/
def handle {T : Signature.{t,r}} {H : Type h}
    (c : Coalgebra S B A X) (handler : Handler S H) : Coalgebra T B A (X × H) :=
  fun (x, h) =>
    match c x with
    | .ret a => .ret a
    | .tau next => .tau (next, h)
    | .vis q next =>
      let (reply, h') := handler h q
      .tau (next reply, h')
    | .branch kind shape next => .branch kind shape fun i => (next i, h)

end Coalgebra

inductive End (S : Signature.{u,v}) (A : Type y) where
  | returned (value : A)
  | stuck (q : S.Request)
  | deadlock (kind : ChoiceKind)
  | diverge

/-- Complete observations. A finite exchange list has an explicit ending.
An infinite observation records a stream of completed exchanges. -/
inductive Trace (S : Signature.{u,v}) (A : Type y) where
  | finite (events : List S.Exchange) (ending : End S A)
  | infinite (events : Nat → S.Exchange)

namespace Coalgebra

variable {S : Signature.{u,v}} {B : Signature.{w,x}}
variable {A : Type y} {X : Type z} (c : Coalgebra S B A X)

/-- A finite prefix of a run, with silent moves bundled before each exchange. -/
inductive Follows : X → List S.Exchange → X → Prop where
  | nil (x : X) : Follows x [] x
  | cons {x y z : X} {e : S.Exchange} {es : List S.Exchange} :
      WeakStep c x e y → Follows y es z → Follows x (e :: es) z

def EndsAt (x : X) : End S A → Prop
  | .returned a => c x = .ret a
  | .stuck q => IsEmpty (S.Response q) ∧ ∃ next, c x = .vis q next
  | .deadlock kind => ∃ shape, IsEmpty (B.Response shape) ∧
      ∃ next, c x = .branch kind shape next
  | .diverge => InfiniteTrace (Internal c) x

/-- An infinite exchange stream must come from a single compatible infinite
state path, with a finite silent segment per exchange. -/
def RunsInfinite (x : X) (events : Nat → S.Exchange) : Prop :=
  ∃ path : Nat → X, path 0 = x ∧ ∀ n, WeakStep c (path n) (events n) (path (n + 1))

def observes (x : X) : Set (Trace S A) := {trace |
  match trace with
  | .finite es ending => ∃ y z, Follows c x es y ∧ Silent c y z ∧ EndsAt c z ending
  | .infinite es => RunsInfinite c x es}

end Coalgebra

/-- May observations across a forest's roots. Each observation comes from
a single root. -/
def Forest.observes {S : Signature.{u,v}} {B : Signature.{w,x}} {A : Type y}
    {I : Type z} (forest : Forest S B A I) : Set (Trace S A) :=
  {t | ∃ i, t ∈ forest.unfold.observes (forest.root i)}

def Refines {S : Signature.{u,v}} {A : Type y} (implementation specification : Set (Trace S A)) :
    Prop := implementation ⊆ specification

def ObsEq {S : Signature.{u,v}} {A : Type y} (left right : Set (Trace S A)) : Prop :=
  left = right

end Silmaril.Semantics.TrackA.Interaction
