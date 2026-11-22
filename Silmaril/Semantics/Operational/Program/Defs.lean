module

public import Silmaril.Semantics.Operational.Policy.Defs

@[expose] public section

namespace Silmaril.Semantics.Operational

universe p q s t o v
variable {Program : Type p} {Other : Type q} {State : Type s} {Target : Type t}
  {Obs : Type o} {View : Type v}

/-- Project non-trap payloads (for example, an `Except Error Result`). Traps
stay distinct from both successful returns and explicit language errors. -/
def Outcome.map (view : Obs → View) : Outcome Obs → Outcome View
  | .trap => .trap
  | .returned value => .returned (view value)

def WithUB.mapObservations (sem : WithUB State Obs) (view : Obs → View) : WithUB State View where
  step := sem.step
  ub := sem.ub
  observe state result := ∃ original, sem.observe state original ∧ original.map view = result

/-- A present state with no primitive move or classification. Host callouts
need a separate observation if pending requests must be distinguished here. -/
def WithUB.Stuck (sem : WithUB State Obs) (state : State) : Prop :=
  ¬ sem.ub state ∧ sem.toOpSem.Normal state ∧ ∀ outcome, ¬ sem.observe state outcome

namespace HasOpSem

def precompose (model : HasOpSem Program State Obs) (erase : Other → Program) : HasOpSem Other State Obs :=
  ⟨fun input => model.initial (erase input), model.semantics⟩

def restrictPrograms (model : HasOpSem Program State Obs) (admitted : Program → Prop) :
    HasOpSem (Subtype admitted) State Obs := model.precompose Subtype.val

def restrictStates (model : HasOpSem Program State Obs) (admitted : State → Prop) :
    HasOpSem Program (Subtype admitted) Obs :=
  ⟨fun program state => model.initial program state.val, model.semantics.restrict admitted⟩

/-- Select only states from which no UB is reachable. This can remove an
entry; forgetting UB via `.semantics.toOpSem` does not remove any entry. -/
def safeFragment (model : HasOpSem Program State Obs) : HasOpSem Program (Subtype model.semantics.SafeAt) Obs :=
  model.restrictStates model.semantics.SafeAt

def mapObservations (model : HasOpSem Program State Obs) (view : Obs → View) : HasOpSem Program State View :=
  ⟨model.initial, model.semantics.mapObservations view⟩

def NoEntry (model : HasOpSem Program State Obs) (program : Program) : Prop := ¬ ∃ start, model.initial program start

/-- Relational sets of finite outcomes, not an effect of running with fuel. -/
def behaviors (model : HasOpSem Program State Obs) (program : Program) : Set (Outcome Obs) :=
  { outcome | model.May program outcome }

def SameFinite (left : HasOpSem Program State Obs) (program : Program)
    (right : HasOpSem Other Target Obs) (other : Other) : Prop := left.behaviors program = right.behaviors other

/-- No new reachable UB. The implication goes from implementation to
specification (equivalently, safety goes the other way). -/
def UBRefines (implementation : HasOpSem Program State Obs) (program : Program)
    (specification : HasOpSem Other Target Obs) (other : Other) : Prop :=
  implementation.UBReachable program → specification.UBReachable other

/-- UB reduction and unconditional finite behavior inclusion. Neither this
nor its symmetric form reflects deadlock, divergence, or missing entries. -/
def Refines (implementation : HasOpSem Program State Obs) (program : Program)
    (specification : HasOpSem Other Target Obs) (other : Other) : Prop :=
  implementation.UBRefines program specification other ∧
    implementation.behaviors program ⊆ specification.behaviors other

def Equivalent (left : HasOpSem Program State Obs) (program : Program)
    (right : HasOpSem Other Target Obs) (other : Other) : Prop :=
  left.Refines program right other ∧ right.Refines other left program

end HasOpSem

end Silmaril.Semantics.Operational
