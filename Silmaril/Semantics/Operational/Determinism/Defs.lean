module

public import Silmaril.Semantics.Operational.Policy.Defs

@[expose] public section

namespace Silmaril.Semantics.Operational

variable {S O K L : Type*}

namespace OpSem

/-- Primitive successor uniqueness. A dead end satisfies this predicate. -/
def StepDetAt (sem : OpSem S O) (source : S) : Prop :=
  ∀ ⦃left right⦄, sem.step source left → sem.step source right → left = right

/-- Primitive successor and immediate observation uniqueness, not progress. -/
def LocalDetAt (sem : OpSem S O) (source : S) : Prop :=
  sem.StepDetAt source ∧ ∀ ⦃left right⦄, sem.observe source left → sem.observe source right → left = right

/-- First take all finite relational outcomes, then compare what the observer sees.
`none` omits an outcome from the uniqueness test, not from execution. -/
def ViewDetAt (sem : OpSem S O) (view : Outcome O → Option K) (start : S) : Prop :=
  ∀ ⦃left right key₁ key₂⦄, sem.May start left → sem.May start right →
    view left = some key₁ → view right = some key₂ → key₁ = key₂

def ResultDetAt (sem : OpSem S O) (start : S) : Prop := sem.ViewDetAt some start

def returnView : Outcome O → Option O
  | .returned value => some value
  | .trap => none

/-- At most one non-trap payload. Trap can coexist with a unique return, and
this predicate says nothing about divergence, must-return, or when traps occur. -/
def NonTrapDetAt (sem : OpSem S O) (start : S) : Prop := sem.ViewDetAt returnView start

/-- Prefix closure is taken against the original relation, before gating. -/
def PrefixGood (sem : OpSem S O) (good : S → Prop) (start : S) : Prop :=
  ∀ ⦃target⦄, sem.Reach start target → good target

end OpSem

/-- A specified observation protocol on a relational machine. Silent steps do
not enter the log; inputs (if modelled here) are explicit labels, not choices
which can silently be assumed fixed. -/
structure Labelled (S L O : Type*) where
  step : S → Option L → S → Prop
  observe : S → Outcome O → Prop

namespace Labelled

inductive Path (sem : Labelled S L O) : S → List L → S → Prop where
  | nil (state : S) : Path sem state [] state
  | silent {source target final log} : sem.step source none target →
      Path sem target log final → Path sem source log final
  | visible {source target final log label} : sem.step source (some label) target →
      Path sem target log final → Path sem source (label :: log) final

def Finishes (sem : Labelled S L O) (start : S) (log : List L) (outcome : Outcome O) : Prop :=
  ∃ final, sem.Path start log final ∧ sem.observe final outcome

/-- Uniqueness of complete finite observed traces (log plus result), not of
all prefixes, and not of infinite interaction traces. Fix incoming messages
in the observer when testing determinism conditional on a host schedule. -/
def TraceDetAt (sem : Labelled S L O) (start : S) : Prop :=
  ∀ ⦃log₁ log₂ result₁ result₂⦄, sem.Finishes start log₁ result₁ → sem.Finishes start log₂ result₂ →
    log₁ = log₂ ∧ result₁ = result₂

end Labelled

namespace WithUB

/-- Stop at the first locally ambiguous primitive state. The edge into that
state (if any) survives. No successor is picked to break a tie. -/
def requireLocalDet (sem : WithUB S O) : WithUB S O := sem.enforce sem.toOpSem.LocalDetAt

/-- Reject earlier: a possible violation on any original prefix invalidates
the current source, whether or not that prefix would have taken the machine there. -/
def requirePrefix (sem : WithUB S O) (good : S → Prop) : WithUB S O :=
  sem.enforce (sem.toOpSem.PrefixGood good)

/-- Compare normalized finite outcomes of the original machine. This relational
guard is not an algorithm for finding out whether evaluation is ambiguous. -/
def requireViewDet (sem : WithUB S O) (view : Outcome O → Option K) : WithUB S O :=
  sem.enforce (sem.toOpSem.ViewDetAt view)

/-- More permissive: ordinary relation inclusion and **reverse** inclusion of
immediate UB. Distinct from both `Included` and safe may-refinement. -/
def Permits (larger smaller : WithUB S O) : Prop :=
  smaller.toOpSem.Sound larger.toOpSem ∧ ∀ ⦃source⦄, larger.ub source → smaller.ub source

def permitJoin (left right : WithUB S O) : WithUB S O where
  toOpSem := (left.join right).toOpSem
  ub source := left.ub source ∧ right.ub source

def permitMeet (left right : WithUB S O) : WithUB S O where
  toOpSem := (left.meet right).toOpSem
  ub source := left.ub source ∨ right.ub source

end WithUB

end Silmaril.Semantics.Operational
