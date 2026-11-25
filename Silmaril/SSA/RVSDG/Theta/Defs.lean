module

public import Silmaril.SSA.RVSDG.Defs

/-!
# A tail-controlled θ with a primitive/γ body

The body has the carried tuple as its arguments and a two-way continuation
predicate followed by the same tuple as its results. This module keeps the
primitive/γ interfaces and adds a whole-region θ constructor.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Theta

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

abbrev BodyResults {V S : Type u} (carried : Ports (PortType V S)) : Ports (PortType V S) :=
  .control 2 :: carried

/-- A θ term binds the body arguments to the current carried tuple. -/
structure Term (Op : Dialect.{u, v} V S) (carried : Ports (PortType V S))
    (sigs : List (Ports (PortType V S))) where
  body : RVSDG.Term Op carried [] sigs (BodyResults carried)

/-- A θ vertex with a hierarchical body and positional feedback of its carried ports.
Its outer input and output signatures are both `carried`. -/
structure Graph (Op : Dialect.{u, v} V S) (carried : Ports (PortType V S))
    (sigs : List (Ports (PortType V S))) where
  body : RVSDG.Graph Op carried [] sigs (BodyResults carried)

def Term.toGraph (term : Term Op carried sigs) : Graph Op carried sigs :=
  ⟨term.body.toGraph⟩

def Graph.toTerm (graph : Graph Op carried sigs) : Term Op carried sigs :=
  ⟨graph.body.toTerm⟩

/-- Port zero controls whether the updated carried tuple is fed back or returned. -/
def bodyResult (m : Model.{u, v, w} Op) (again : Bool) (values : Tuple m.Val carried) :
    Tuple m.Val (BodyResults carried) :=
  .cons (⟨if again then 1 else 0⟩ : ULift (Fin 2)) values

/-- Finite θ execution. The first body activation is mandatory. -/
inductive Iterate {X : Type w} (body : X → Bool → X → Prop) : X → X → Prop where
  | stop {start finish : X} (last : body start false finish) : Iterate body start finish
  | again {start next finish : X} (step : body start true next) (rest : Iterate body next finish) :
      Iterate body start finish

/-- An infinite sequence of body completions, each requesting another iteration. -/
def Repeats {X : Type w} (body : X → Bool → X → Prop) (start : X) : Prop :=
  ∃ inputs : Nat → X, inputs 0 = start ∧ ∀ n, body (inputs n) true (inputs (n + 1))

def Term.Returns (term : Term Op carried sigs) (m : Model.{u, v, w} Op) :
    Tuple m.Val carried → Tuple m.Val carried → Prop :=
  Iterate (fun input again output => term.body.run m input = bodyResult m again output)

def Graph.Returns (graph : Graph Op carried sigs) (m : Model.{u, v, w} Op) :
    Tuple m.Val carried → Tuple m.Val carried → Prop :=
  Iterate (fun input again output => graph.body.run m input = bodyResult m again output)

def Graph.Diverges (graph : Graph Op carried sigs) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val carried) : Prop :=
  Repeats (fun before again after => graph.body.run m before = bodyResult m again after) input

end Silmaril.SSA.RVSDG.Theta
