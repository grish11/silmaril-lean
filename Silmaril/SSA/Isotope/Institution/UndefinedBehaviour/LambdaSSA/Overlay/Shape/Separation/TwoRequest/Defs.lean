module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Defs

/-! # Boolean-dependent two-request LambdaSSA overlays -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest

open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent

abbrev U : Silmaril.Ty Empty := .unit
abbrev Bit : Silmaril.Ty Empty := .coprod U U
abbrev Exits : List (Silmaril.Ty Empty) := List.replicate 2 U

/-- Left and right tags of the exact Boolean sum, also used as ordered exit indices. -/
abbrev Tag := Fin 2

universe v w

def bitValue {α : Type v} (i : Tag) : Value α :=
  if i = 0 then .inl .unit else .inr .unit

def bitPayload (i : Tag) : Syntax.Payload Bit :=
  if i = 0 then ⟨.inl .unit, .inl .unit⟩ else ⟨.inr .unit, .inr .unit⟩

inductive Instr where
  | ask
  | other
  deriving DecidableEq

instance : HasTy Instr (Silmaril.Ty Empty) := ⟨fun _ => U, fun _ => Bit⟩

inductive Exit where
  | ret (label : Tag)
  | ub
  deriving DecidableEq

structure Row where
  key : Instr
  exit : Tag → Exit

/-- The first Boolean reply selects the second request key. Both requests
have literal-unit input. The second Boolean reply selects a continuation. -/
structure Endpoint where
  first : Instr
  next : Tag → Row

/-- A native effectful branch. The primitive reply is inspected exactly once.
Its Boolean tag chooses an ordered exit, carrying unit at the reply state. -/
def request (f : Instr) (Γ : List (Silmaril.Ty Empty)) : Native.Typed Instr Γ Exits :=
  ⟨.case (.op f .unit) (.br 0 .unit) (.br 1 .unit),
    .case (.op (f := f) .unit) (.br (ℓ := 0) rfl .unit) (.br (ℓ := 1) rfl .unit)⟩

theorem exit_type (i : Fin Exits.length) : Exits.get i = U := by simp

def Exit.region (e : Exit) {Γ : List (Silmaril.Ty Empty)} : Overlay.Region Instr Γ Exits :=
  match e with
  | .ret i => .native (Native.jump (L := Exits) i (exit_type i) .unit)
  | .ub => .ub

/-- Observation of a terminal continuation at its incoming state. -/
def Exit.behaviour {α : Type v} {σ : Type w} (e : Exit) (s : σ) :
    Behaviour Exits.length α σ :=
  match e with
  | .ret i => WithTop.some {Outcome.ret i .unit s}
  | .ub => ⊤

def Row.region (r : Row) {Γ : List (Silmaril.Ty Empty)} : Overlay.Region Instr Γ Exits :=
  .lsubst (.native (request r.key Γ)) fun j => (r.exit j).region

def Endpoint.region (p : Endpoint) : Overlay.Region Instr [] Exits :=
  .lsubst (.native (request p.first [])) fun i => (p.next i).region

/-- The right terminal can allow more behaviours by exposing literal UB. -/
def Exit.Refines (p q : Exit) : Prop := q = .ub ∨ p = q

/-- Normal-form order on the full two-request fragment. Request keys are
observable through their effects, even when the final continuation is UB. -/
def NormalRefines (p q : Endpoint) : Prop :=
  p.first = q.first ∧ ∀ i, (p.next i).key = (q.next i).key ∧
    ∀ j, ((p.next i).exit j).Refines ((q.next i).exit j)

inductive Action (states : Nat) where
  | reply (tag : Tag) (final : Fin states)
  | fault (final : Fin states)
  | diverge

def Action.toReply {states : Nat} : Action states → Syntax.Reply Bit states
  | .reply b t => .ret (bitPayload b) t
  | .fault t => .fault t
  | .diverge => .diverge

abbrev Handler (states : Nat) := Instr → Fin states → Action states

def Handler.primitives {states : Nat} (h : Handler states) : Syntax.Primitives Instr states :=
  fun f _ s => (h f s).toReply

abbrev Handler.model {states : Nat} (h : Handler states) :=
  Syntax.model h.primitives Syntax.emptyBindings

/-- A deterministic test accepts at most one key at each prefix state.
A repeat of the same key hits a different row at state one. All other
queries have ordinary primitive divergence. -/
def prefixHandler (first next : Instr) (root step : Action 3) : Handler 3 :=
  fun f s =>
    if s = 0 ∧ f = first then root
    else if s = 1 ∧ f = next then step
    else .diverge

def Exit.result {states : Nat} (exit : Exit) (s : Fin states) : Result 2 states :=
  match exit with
  | .ret i => .ret i s
  | .ub => .ub

def resultBehaviour {states : Nat} : Result 2 states → Behaviour Exits.length Unit (Fin states)
  | .ret i s => WithTop.some {Outcome.ret i .unit s}
  | .fault s => WithTop.some {Outcome.fault s}
  | .diverge => WithTop.some {Outcome.diverge}
  | .ub => ⊤

def Row.execute {states : Nat} (r : Row) (h : Handler states) (s : Fin states) :
    Result 2 states :=
  match h r.key s with
  | .reply j t => (r.exit j).result t
  | .fault t => .fault t
  | .diverge => .diverge

def Endpoint.execute {states : Nat} (p : Endpoint) (h : Handler states) (s : Fin states) :
    Result 2 states :=
  match h p.first s with
  | .reply i t => (p.next i).execute h t
  | .fault t => .fault t
  | .diverge => .diverge

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest
