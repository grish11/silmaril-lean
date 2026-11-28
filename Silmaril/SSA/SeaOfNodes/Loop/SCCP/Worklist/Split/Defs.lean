module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Defs

/-! FIFO control and result jobs with independently scheduled typed Φ destinations. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split

open Diamond (Model Signature Ty ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {value : Data → Type w}

inductive Job (n : Nat) where
  | control
  | phi (dst : Fin n)
  | result
  deriving DecidableEq, Repr

abbrev Task (carried : List (ValueSort Data)) := Job (dataPorts carried).length

/-- Among new jobs, queue control first, then Φ in destination order, then result. -/
def jobs (n : Nat) : List (Job n) :=
  .control :: (List.finRange n).map Job.phi ++ [.result]

def Job.Input (value : Data → Type w) (carried : List (ValueSort Data)) : Task carried → Type w
  | .control => Worklist.Task.Input value carried .control
  | .phi dst => Phi.Watched value carried dst
  | .result => Worklist.Task.Input value carried .result

def Job.Output (value : Data → Type w) (carried : List (ValueSort Data)) (out : ValueSort Data) :
    Task carried → Type w
  | .control => ULift.{w} Executable
  | .phi dst => Fact value (dataPorts carried)[dst]
  | .result => Flat (sortValue value out)

def get (state : State value carried out) : (job : Task carried) → job.Output value carried out
  | .control => Worklist.get state .control
  | .phi dst => state.2.1 dst
  | .result => Worklist.get state .result

def set (state : State value carried out) :
    (job : Task carried) → job.Output value carried out → State value carried out
  | .control, edges => Worklist.set state .control edges
  | .phi dst, fact => Phi.write state dst fact
  | .result, result => Worklist.set state .result result

variable (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts carried)]
variable (g : Graph Op inputs carried entrySigs headerSigs out)
variable (input : Tuple (Fact m.value) (dataPorts inputs))

def dependencies (state : State m.value carried out) : (job : Task carried) → job.Input m.value carried
  | .control => Worklist.dependencies state .control
  | .phi dst => Phi.dependencies m g input state dst
  | .result => Worklist.dependencies state .result

def evaluate : (job : Task carried) → job.Input m.value carried → job.Output m.value carried out
  | .control, watched => Worklist.evaluate m g input .control watched
  | .phi dst, watched => Phi.evaluate m g input dst watched
  | .result, watched => Worklist.evaluate m g input .result watched

instance (job : Task carried) : DecidableEq (job.Input m.value carried) :=
  match job with
  | .control => inferInstanceAs (DecidableEq (Worklist.Task.Input m.value carried .control))
  | .phi dst => inferInstanceAs (DecidableEq (Phi.Watched m.value carried dst))
  | .result => inferInstanceAs (DecidableEq (Worklist.Task.Input m.value carried .result))

def update (job : Task carried) (state : State m.value carried out) : State m.value carried out :=
  set state job (evaluate m g input job (dependencies m g input state job))

/-- Notify jobs by watched-input changes, including enabling entry, feedback,
or exit. Producer-fed Φ jobs compare only their carried operand support. -/
def wake (old new : State m.value carried out) (pending : List (Task carried)) : List (Task carried) :=
  FIFO.wake (jobs (dataPorts carried).length)
    (fun job => decide (dependencies m g input new job ≠ dependencies m g input old job)) pending

def step (job : Task carried) (state : State m.value carried out) (pending : List (Task carried)) :
    State m.value carried out × List (Task carried) :=
  let new := update m g input job state
  (new, wake m g input state new pending)

/-- Every equation whose job is absent from the queue is already satisfied. -/
def Stable (state : State m.value carried out) (pending : List (Task carried)) : Prop :=
  ∀ job, job ∉ pending → get (SCCP.transfer m g input state) job = get state job

abbrev Run (value : Data → Type w) (carried : List (ValueSort Data)) (out : ValueSort Data) :=
  FIFO.Run (State value carried out) (Task carried)

def runSteps : Nat → State m.value carried out → List (Task carried) → Run m.value carried out :=
  FIFO.runSteps (step m g input)

def potential (state : State value carried out) (pending : List (Task carried)) : Nat :=
  FIFO.potential (height value carried out) (dataPorts carried).length.succ.succ state pending

def initial : List (Task carried) := [.control]

/-- Evaluate from optimistic bottom with enough fuel to drain the FIFO. -/
def run : Run m.value carried out :=
  runSteps m g input (potential (⊥ : State m.value carried out) initial) ⊥ initial

def solve : State m.value carried out := (run m g input).state

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split
