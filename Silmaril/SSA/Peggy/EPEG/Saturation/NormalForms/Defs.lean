module

public import Mathlib.Logic.Relation

/-! # Stable normal forms for families of saturation analyses -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms

universe u v

variable {State : Type u} {Label : Type v}

abbrev Analysis (State : Type u) := State → State → Prop
abbrev Family (State : Type u) (Label : Type v) := Label → Analysis State

/-- Equation (4.1) for a single analysis. -/
def Inflationary (order : State → State → Prop) (analysis : Analysis State) : Prop :=
  ∀ ⦃source target⦄, analysis source target → order source target

/-- Equation (4.2). The simulated step may be a stutter. -/
def MonotoneSimulation (order : State → State → Prop) (analysis : Analysis State) : Prop :=
  ∀ ⦃small large smallNext⦄, order small large → analysis small smallNext →
    ∃ largeNext, analysis large largeNext ∧ order smallNext largeNext

def Step (family : Family State Label) (source target : State) : Prop :=
  ∃ label, family label source target

abbrev Reachable (family : Family State Label) :=
  Relation.ReflTransGen (Step family)

/-- The target of every analysis step is covered by the current state.
Inflationarity makes such steps equivalent in both directions. -/
def Stable (order : State → State → Prop) (family : Family State Label) (state : State) : Prop :=
  ∀ ⦃target⦄, Step family state target → order target state

def StableNormalForm (order : State → State → Prop) (family : Family State Label)
    (source target : State) : Prop :=
  Reachable family source target ∧ Stable order family target

def Progress (order : State → State → Prop) (family : Family State Label)
    (source target : State) : Prop :=
  Step family source target ∧ ¬ order target source

/-- Section 4 filters out steps with literally identical endpoints. -/
def PaperStep (family : Family State Label) (source target : State) : Prop :=
  Step family source target ∧ source ≠ target

def PaperNormalForm (family : Family State Label) (source target : State) : Prop :=
  Relation.ReflTransGen (PaperStep family) source target ∧
    ∀ next, ¬ PaperStep family target next

end Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms
