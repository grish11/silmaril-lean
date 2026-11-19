module

public import Silmaril.Semantics.Region.Effects.Defs

/-! # Indexed effect and function-pair problems

Indices may be symbolic arguments, abstract entry states or argument/result
pairs. Representation and observations are supplied by the client. There is
no implied calling convention, machine memory, feasibility or termination.
-/

@[expose] public section
namespace Silmaril.Semantics.Function.Effects
universe u v w x y

structure Problem (Index : Type u) (Effect : Type v) where
  Observation : Type w
  occurs : Index → Observation → Prop
  observe : Observation → Effect

abbrev OnArgs := Problem
abbrev OnEntry := Problem
abbrev OnResult (Args : Type u) (Result : Type v) (Effect : Type w) := Problem (Args × Result) Effect

def Problem.Sound {Index : Type u} {Effect : Type v} [LE Effect]
    (problem : Problem Index Effect) (summary : Index → Effect) : Prop :=
  ∀ index event, problem.occurs index event → problem.observe event ≤ summary index

noncomputable def Problem.least {Index : Type u} {Effect : Type v} [CompleteLattice Effect]
    (problem : Problem Index Effect) : Index → Effect :=
  fun index => ⨆ event, ⨆ (_ : problem.occurs index event), problem.observe event

/-- All concrete inputs represented by an abstract argument contribute. -/
def Problem.abstractInput {Index : Type u} {Concrete : Type v} {Effect : Type w}
    (problem : Problem Concrete Effect) (represents : Index → Concrete → Prop) : Problem Index Effect where
  Observation := problem.Observation
  occurs index event := ∃ input, represents index input ∧ problem.occurs input event
  observe := problem.observe

open Silmaril.Semantics.Region in
def forRegion {State : Type u} {Label : Type v} {Event : Type w} {Stop : Type x} {Effect : Type y}
    (machine : TransitionSystem State Label Event Stop) (support : Label → Prop)
    (observe : Sum Event Stop → Effect) : Problem State Effect :=
  ⟨Sum Event Stop, fun entry => Region.Effects.MayObservation machine (· = entry) support, observe⟩

open Silmaril.Semantics.Region in
def ExitSound {State : Type u} {Label : Type v} {Event : Type w} {Stop : Type x}
    (machine : TransitionSystem State Label Event Stop) (support : Label → Prop)
    (admit : State → Prop) (exits : Label → List Event → State → Prop)
    (halts : Stop → List Event → State → Prop) : Prop :=
  ∀ state, admit state → wp machine support exits halts state

/-- A relational summary preserves possible intermediate states. A joined
effect envelope alone is not a witness to an input-dependent path. -/
abbrev Summary (Input : Type u) (Output : Type v) (Effect : Type w) :=
  Input → Output → Effect → Prop

def sequence {Input : Type u} {Middle : Type v} {Output : Type w} {Effect : Type x}
    (combine : Effect → Effect → Effect) (first : Summary Input Middle Effect)
    (second : Summary Middle Output Effect) : Summary Input Output Effect :=
  fun input output effect => ∃ mid left right,
    first input mid left ∧ second mid output right ∧ effect = combine left right

def Refines {Input : Type u} {Output : Type v} {Effect : Type w}
    (actual possible : Summary Input Output Effect) : Prop :=
  ∀ ⦃input output effect⦄, actual input output effect → possible input output effect

end Silmaril.Semantics.Function.Effects
