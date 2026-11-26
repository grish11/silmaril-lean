module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Defs

/-! Dependency-triggered FIFO iteration of the native loop equations. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {value : Data → Type w}

inductive Task where
  | control
  | phi
  | result
  deriving DecidableEq, Repr

/-- A job only watches bank facts when its corresponding occurrence is marked.
Phi watches both incoming marks and reads the bank only for feedback. -/
def Task.Input (value : Data → Type w) (carried : List (ValueSort Data)) : Task → Type w
  | .control | .result => Option (BankFacts value (dataPorts carried))
  | .phi => Executable × Option (BankFacts value (dataPorts carried))

def Task.Output (value : Data → Type w) (carried : List (ValueSort Data)) (out : ValueSort Data) :
    Task → Type w
  | .control => ULift.{w} Executable
  | .phi => BankFacts value (dataPorts carried)
  | .result => Flat (sortValue value out)

def dependencies (state : State value carried out) : (job : Task) → job.Input value carried
  | .control => if incomingIndex .entry ∈ state.1 then some state.2.1 else none
  | .phi => (state.1.erase exitIndex, if incomingIndex .backedge ∈ state.1 then some state.2.1 else none)
  | .result => if exitIndex ∈ state.1 then some state.2.1 else none

def get (state : State value carried out) : (job : Task) → job.Output value carried out
  | .control => ⟨state.1⟩
  | .phi => state.2.1
  | .result => state.2.2

def set (state : State value carried out) : (job : Task) → job.Output value carried out → State value carried out
  | .control, edges => (edges.down, state.2)
  | .phi, bank => (state.1, bank, state.2.2)
  | .result, result => (state.1, state.2.1, result)

variable [eqBank : BankDecidableEq value (dataPorts carried)]

instance (job : Task) : DecidableEq (job.Input value carried) :=
  let _ : ∀ i : Fin (dataPorts carried).length, DecidableEq (Fact value (dataPorts carried)[i]) :=
    fun i => @Semantics.Dataflow.instDecidableEqFlat _ (eqBank.atPort i)
  let _ : DecidableEq (BankFacts value (dataPorts carried)) := Fintype.decidablePiFintype
  match job with
  | .control | .result => inferInstanceAs (DecidableEq (Option (BankFacts value (dataPorts carried))))
  | .phi => inferInstanceAs (DecidableEq (Executable × Option (BankFacts value (dataPorts carried))))

/-- Append a triggered job only when it has no pending copy. -/
def schedule (changed : Prop) [Decidable changed] (job : Task) (pending : List Task) : List Task :=
  if changed ∧ job ∉ pending then pending ++ [job] else pending

def scheduleChanged (old new : State value carried out) (job : Task) (pending : List Task) : List Task :=
  schedule (dependencies new job ≠ dependencies old job) job pending

/-- Wake only jobs whose watched inputs changed. No equation is evaluated here. -/
def wake (old new : State value carried out) (pending : List Task) : List Task :=
  scheduleChanged old new .result (scheduleChanged old new .phi (scheduleChanged old new .control pending))

variable (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts carried)]
variable (g : Graph Op inputs carried entrySigs headerSigs out)
variable (input : Tuple (Fact m.value) (dataPorts inputs))

def evaluate : (job : Task) → job.Input m.value carried → job.Output m.value carried out
  | .control, none => ⟨({incomingIndex .entry} : Executable)⟩
  | .control, some bank => ⟨control {incomingIndex .entry} (headerFacts m g input bank).guard⟩
  | .phi, (edges, bank) =>
    let feedback := match bank with
      | none => ⊥
      | some old => (headerFacts m g input old).feedback
    phiFacts edges (entryFacts m g input) feedback
  | .result, none => Flat.bottom
  | .result, some bank => (headerFacts m g input bank).result

def update (job : Task) (state : State m.value carried out) : State m.value carried out :=
  set state job (evaluate m g input job (dependencies state job))

/-- Process a single equation, then notify jobs that read the changed facts. -/
def step (job : Task) (state : State m.value carried out) (pending : List Task) :
    State m.value carried out × List Task :=
  let new := update m g input job state
  (new, wake state new pending)

structure Run (value : Data → Type w) (carried : List (ValueSort Data)) (out : ValueSort Data) where
  state : State value carried out
  pending : List Task
  visits : List Task

def runSteps (fuel : Nat) (state : State m.value carried out) (pending : List Task) : Run m.value carried out :=
  let result := FIFO.runSteps (step m g input) fuel state pending
  ⟨result.state, result.pending, result.visits⟩

/-- Each strict ascent pays for at most three insertions. Without an ascent,
the popped job reduces the queue length. -/
def potential (state : State value carried out) (pending : List Task) : Nat :=
  FIFO.potential (height value carried out) 3 state pending

/-- The bottom assignment satisfies the bank and result equations. Start
only needs to enable entry. -/
def initial : List Task := [.control]

def run : Run m.value carried out :=
  runSteps m g input (potential (⊥ : State m.value carried out) initial) ⊥ initial

def solve : State m.value carried out := (run m g input).state

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist
