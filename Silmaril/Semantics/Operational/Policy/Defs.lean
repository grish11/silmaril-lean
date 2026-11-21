module

public import Silmaril.Foundations.InfiniteTrace

@[expose] public section

namespace Silmaril.Semantics.Operational

universe u v w x

/-- Finite observations. Neither a trap nor a return is undefined behaviour. -/
inductive Outcome (Obs : Type v) where
  | returned (value : Obs)
  | trap

/-- An unlabelled transition relation and a finite-observation relation.
No transition or observation at a state means only that neither is supplied.
Terminal discipline, determinism and progress are separate properties. -/
structure OpSem (State : Type u) (Obs : Type v) where
  step : State → State → Prop
  observe : State → Outcome Obs → Prop

structure WithUB (State : Type u) (Obs : Type v) extends OpSem State Obs where
  ub : State → Prop

/-- A semantics value, not a global instance. Program can be a function entry
with arguments, a module with imports, or a component with its environment.
A version/profile tag can select a value without changing the syntax type. -/
structure HasOpSem (Program : Type w) (State : Type u) (Obs : Type v) where
  initial : Program → State → Prop
  semantics : WithUB State Obs

variable {S : Type u} {T : Type w} {Obs : Type v}

namespace OpSem

abbrev Reach (sem : OpSem S Obs) := Relation.ReflTransGen sem.step

def May (sem : OpSem S Obs) (source : S) (outcome : Outcome Obs) : Prop :=
  ∃ target, sem.Reach source target ∧ sem.observe target outcome

def TrapReachable (sem : OpSem S Obs) (source : S) : Prop := sem.May source .trap

def Normal (sem : OpSem S Obs) (source : S) : Prop := ∀ target, ¬ sem.step source target

def Diverges (sem : OpSem S Obs) (source : S) : Prop := InfiniteTrace sem.step source

def TerminalDiscipline (sem : OpSem S Obs) : Prop :=
  ∀ ⦃source outcome⦄, sem.observe source outcome → sem.Normal source

/-- This says 'at most one', not progress and not unique initialization. -/
def DetFrom (sem : OpSem S Obs) (start : S) : Prop :=
  ∀ ⦃source⦄, sem.Reach start source →
    (∀ ⦃left right⦄, sem.step source left → sem.step source right → left = right) ∧
    (∀ ⦃left right⦄, sem.observe source left → sem.observe source right → left = right)

/-- Same-state pointwise inclusion, not inclusion of maximal executions. -/
def Includes (reference candidate : OpSem S Obs) : Prop :=
  (∀ ⦃source target⦄, candidate.step source target → reference.step source target) ∧
  (∀ ⦃source outcome⦄, candidate.observe source outcome → reference.observe source outcome)

def Sound (candidate reference : OpSem S Obs) : Prop := reference.Includes candidate

def Complete (candidate reference : OpSem S Obs) : Prop := candidate.Includes reference

/-- Pointwise inclusion restricted at the source of steps and observations. -/
def SoundOn (candidate reference : OpSem S Obs) (guard : S → Prop) : Prop :=
  ∀ ⦃source⦄, guard source →
    (∀ ⦃target⦄, candidate.step source target → reference.step source target) ∧
    (∀ ⦃outcome⦄, candidate.observe source outcome → reference.observe source outcome)

end OpSem

namespace WithUB

def UBReachable (sem : WithUB S Obs) (start : S) : Prop :=
  ∃ target, sem.toOpSem.Reach start target ∧ sem.ub target

/-- Demonic safety: no path (including the empty path) can reach UB. -/
def SafeAt (sem : WithUB S Obs) (start : S) : Prop := ¬ sem.UBReachable start

def SafeOn (sem : WithUB S Obs) (admissible : S → Prop) : Prop :=
  ∀ ⦃start⦄, admissible start → sem.SafeAt start

def ofOpSem (sem : OpSem S Obs) : WithUB S Obs := ⟨sem, fun _ => False⟩

/-- A typing/feature/encodability policy supplied by the caller. Invalid sources
are UB and have no step or observation. A valid step to an invalid target is
retained, so leaving the policy region is observable as reachable UB. -/
def enforce (sem : WithUB S Obs) (good : S → Prop) : WithUB S Obs where
  step source target := good source ∧ sem.step source target
  observe source outcome := good source ∧ sem.observe source outcome
  ub source := sem.ub source ∨ ¬ good source

/-- Induced submachine (crossing edges are dropped, not reported as UB). -/
def restrict (sem : WithUB S Obs) (good : S → Prop) : WithUB (Subtype good) Obs where
  step source target := sem.step source.val target.val
  observe source outcome := sem.observe source.val outcome
  ub source := sem.ub source.val

/-- May-image under a state map. A non-injective map can splice paths and pool
observations. `Compatible` is the explicit condition for path readback. -/
def push (sem : WithUB S Obs) (map : S → T) : WithUB T Obs where
  step source target := ∃ left right, map left = source ∧ map right = target ∧ sem.step left right
  observe source outcome := ∃ left, map left = source ∧ sem.observe left outcome
  ub source := ∃ left, map left = source ∧ sem.ub left

structure Compatible (sem : WithUB S Obs) (map : S → T) : Prop where
  step : ∀ ⦃left source target⦄, map left = map source → sem.step left target →
    ∃ right, sem.step source right ∧ map right = map target
  observe : ∀ ⦃left source outcome⦄, map left = map source → sem.observe left outcome →
    sem.observe source outcome
  ub : ∀ ⦃left source⦄, map left = map source → sem.ub left → sem.ub source

def quotient (sem : WithUB S Obs) (setoid : Setoid S) : WithUB (Quotient setoid) Obs :=
  sem.push (Quotient.mk setoid)

/-- When the map is injective this extends a smaller machine with UB outside
its image. It adds no steps, traps or returns outside the image. -/
def lift (sem : WithUB S Obs) (map : S → T) : WithUB T Obs where
  toOpSem := (sem.push map).toOpSem
  ub source := (sem.push map).ub source ∨ ¬ ∃ left, map left = source

/-- Mixed refinement, intentionally not the componentwise inclusion order:
on specified safe inputs, the implementation stays safe and adds no finite
observations. This is not a must-, progress- or trace-refinement judgment. -/
def SafeRefines (implementation specification : WithUB S Obs) : Prop :=
  ∀ ⦃start⦄, specification.SafeAt start → implementation.SafeAt start ∧
    ∀ ⦃outcome⦄, implementation.toOpSem.May start outcome → specification.toOpSem.May start outcome

/-- Compare ordinary steps and observations only where both machines are safe. -/
def AgreeWhenSafe (left right : WithUB S Obs) : Prop :=
  left.toOpSem.SoundOn right.toOpSem (fun s => left.SafeAt s ∧ right.SafeAt s) ∧
  right.toOpSem.SoundOn left.toOpSem (fun s => left.SafeAt s ∧ right.SafeAt s)

/-- Inclusion of all three primitive relations (not `SafeRefines`). -/
def Included (left right : WithUB S Obs) : Prop :=
  left.toOpSem.Sound right.toOpSem ∧ ∀ ⦃source⦄, left.ub source → right.ub source

def meet (left right : WithUB S Obs) : WithUB S Obs where
  step source target := left.step source target ∧ right.step source target
  observe source outcome := left.observe source outcome ∧ right.observe source outcome
  ub source := left.ub source ∧ right.ub source

def join (left right : WithUB S Obs) : WithUB S Obs where
  step source target := left.step source target ∨ right.step source target
  observe source outcome := left.observe source outcome ∨ right.observe source outcome
  ub source := left.ub source ∨ right.ub source

end WithUB

namespace HasOpSem

variable {Program : Type w}

def May (model : HasOpSem Program S Obs) (program : Program) (outcome : Outcome Obs) : Prop :=
  ∃ start, model.initial program start ∧ model.semantics.toOpSem.May start outcome

def UBReachable (model : HasOpSem Program S Obs) (program : Program) : Prop :=
  ∃ start, model.initial program start ∧ model.semantics.UBReachable start

end HasOpSem

/-- A forward simulation: a left step is matched by a finite right path
(possibly empty), preserving the unchanged observation alphabet and UB.
It transfers may-outcomes and possible UB left-to-right, not divergence. -/
structure OpSim (left : WithUB S Obs) (right : WithUB T Obs) (rel : S → T → Prop) : Prop where
  step : ∀ ⦃source matched next⦄, rel source matched → left.step source next →
    ∃ target, right.toOpSem.Reach matched target ∧ rel next target
  observe : ∀ ⦃source matched outcome⦄, rel source matched → left.observe source outcome →
    right.toOpSem.May matched outcome
  ub : ∀ ⦃source matched⦄, rel source matched → left.ub source → right.UBReachable matched

def RelComp {U : Type x} (first : S → T → Prop) (second : T → U → Prop) (source : S) (target : U) : Prop :=
  ∃ middle, first source middle ∧ second middle target

end Silmaril.Semantics.Operational
