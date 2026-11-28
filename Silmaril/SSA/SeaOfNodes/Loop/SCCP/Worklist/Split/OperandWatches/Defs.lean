module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Defs

/-! Opt-in control and result notifications based on typed operand support. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {value : Data → Type w}

structure OperandWatches (g : Graph Op inputs carried entrySigs headerSigs out) where
  index : Index g
  guardPorts : Finset (Phi.Job carried)
  resultPorts : Finset (Phi.Job carried)
  guardPorts_eq : guardPorts = Phi.Support.wire (inputs := inputs) (carried := carried) g.header g.predicate
  resultPorts_eq : resultPorts = Phi.Support.wire (inputs := inputs) (carried := carried) g.header g.result

namespace OperandWatches

variable {g : Graph Op inputs carried entrySigs headerSigs out}

/-- Build the guard and result support from one ranked header table. -/
def build (index : Index g) : OperandWatches g :=
  let args := Phi.Support.headerPorts inputs carried
  let locals := Phi.Support.table args g.header PUnit.unit
  ⟨index, Phi.Support.read args locals g.predicate, Phi.Support.read args locals g.result, rfl, rfl⟩

/-- A changed fact matters to a watch if the popped destination is in its support. -/
def hits (job : Task carried) (support : Finset (Phi.Job carried)) (bankChanged : Bool) : Bool :=
  match job with
  | .phi field => bankChanged && decide (field ∈ support)
  | .control | .result => false

def candidateChanged (watches : OperandWatches g) (job : Task carried)
    (old new : Executable) (bankChanged : Bool) : Task carried → Bool
  | .control => Index.gatedBankChanged (incomingIndex .entry) old new (hits job watches.guardPorts bankChanged)
  | .phi _ => true
  | .result => Index.gatedBankChanged exitIndex old new (hits job watches.resultPorts bankChanged)

/-- Notify after one pop. Mark toggles retain the reference wake behavior. -/
def wakeAfter [BankDecidableEq value (dataPorts carried)]
    (watches : OperandWatches g) (job : Task carried) (old new : State value carried out)
    (pending : List (Task carried)) : List (Task carried) :=
  let changed := Index.bankChangedAfter job old new
  let destinations := watches.index.destinationsFromWrite job old.1 new.1 changed
  Index.wakeCandidates destinations (watches.candidateChanged job old.1 new.1 changed) pending

variable (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts carried)]
variable (input : Tuple (Fact m.value) (dataPorts inputs))

def step (watches : OperandWatches g) (job : Task carried) (state : State m.value carried out)
    (pending : List (Task carried)) : State m.value carried out × List (Task carried) :=
  let new := Split.update m g input job state
  (new, wakeAfter watches job state new pending)

def runSteps (watches : OperandWatches g) : Nat → State m.value carried out → List (Task carried) → Run m.value carried out :=
  FIFO.runSteps (step m input watches)

def run (watches : OperandWatches g) : Run m.value carried out :=
  runSteps m input watches (potential (⊥ : State m.value carried out) initial) ⊥ initial

def solve (watches : OperandWatches g) : State m.value carried out := (run m input watches).state

end OperandWatches
end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split
