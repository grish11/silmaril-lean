module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Defs

/-! Run the typed two-route quad equations with dependency-triggered FIFO jobs. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist

open SeaOfNodes.Diamond (Model Signature ValueSort dataPorts sortValue)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq BankFacts bankTuple)
open SeaOfNodes.Loop.SCCP.Worklist
open SeaOfNodes.Loop.SCCP.Worklist.Split (Job Task jobs)
open Semantics.Dataflow (Flat)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {value : Data → Type w}

/-- Control and result watch a marked bank. Each typed Φ destination
watches the incoming marks and reads the carried bank only for feedback. -/
def Watched (value : Data → Type w) (regs : List (ValueSort Data)) : Task regs → Type w
  | .control | .result => Option (BankFacts value (dataPorts regs))
  | .phi _ => Marked × Option (BankFacts value (dataPorts regs))

def Output (value : Data → Type w) (regs : List (ValueSort Data)) (out : ValueSort Data) : Task regs → Type w
  | .control => ULift.{w} Marked
  | .phi dst => Fact value (dataPorts regs)[dst]
  | .result => Flat (sortValue value out)

def dependencies (state : State value regs out) : (job : Task regs) → Watched value regs job
  | .control => if incomingIndex .entry ∈ state.1 then some state.2.1 else none
  | .phi _ => (state.1.erase exitIndex,
      if incomingIndex (.feedback true) ∈ state.1 ∨ incomingIndex (.feedback false) ∈ state.1 then
        some state.2.1 else none)
  | .result => if exitIndex ∈ state.1 then some state.2.1 else none

def get (state : State value regs out) : (job : Task regs) → Output value regs out job
  | .control => ⟨state.1⟩
  | .phi dst => state.2.1 dst
  | .result => state.2.2

def set (state : State value regs out) :
    (job : Task regs) → Output value regs out job → State value regs out
  | .control, marks => (marks.down, state.2)
  | .phi dst, fact => (state.1, Function.update state.2.1 dst fact, state.2.2)
  | .result, fact => (state.1, state.2.1, fact)

variable [equal : BankDecidableEq value (dataPorts regs)]

instance (job : Task regs) : DecidableEq (Watched value regs job) :=
  let _ : ∀ i : Fin (dataPorts regs).length, DecidableEq (Fact value (dataPorts regs)[i]) :=
    fun i => @Semantics.Dataflow.instDecidableEqFlat _ (equal.atPort i)
  let _ : DecidableEq (BankFacts value (dataPorts regs)) := Fintype.decidablePiFintype
  match job with
  | .control | .result => inferInstanceAs (DecidableEq (Option (BankFacts value (dataPorts regs))))
  | .phi _ => inferInstanceAs (DecidableEq (Marked × Option (BankFacts value (dataPorts regs))))

variable (m : Model.{u, v, w} Op) (p : Program Op regs out) [BankDecidableEq m.value (dataPorts regs)]
variable (input : Tuple (Fact m.value) (dataPorts regs))

/-- Evaluate the selected equation with the shared abstract block and Φ
evaluators. Disabled predecessor columns are never evaluated by a Φ pop. -/
def evaluate : (job : Task regs) → Watched m.value regs job → Output m.value regs out job
  | .control, none => ⟨{incomingIndex .entry}⟩
  | .control, some bank =>
    let current := blockFacts m p.header (bankTuple bank)
    ⟨insert (incomingIndex .entry) (successors (current.get p.again) (current.get p.select))⟩
  | .phi dst, (marks, bank) =>
    let current := match bank with
      | some carried => blockFacts m p.header (bankTuple carried)
      | none => bankTuple ⊥
    phiFacts marks (fun edge => if incomingIndex edge ∈ marks then columns m p input current edge else ⊥) dst
  | .result, none => Flat.bottom
  | .result, some bank => (blockFacts m p.header (bankTuple bank)).get p.result

def update (job : Task regs) (state : State m.value regs out) : State m.value regs out :=
  set state job (evaluate m p input job (dependencies state job))

/-- A pop only schedules absent jobs whose watched inputs have changed. -/
def wake (old new : State value regs out) (pending : List (Task regs)) : List (Task regs) :=
  FIFO.wake (jobs (dataPorts regs).length)
    (fun job => decide (dependencies new job ≠ dependencies old job)) pending

def step (job : Task regs) (state : State m.value regs out) (pending : List (Task regs)) :
    State m.value regs out × List (Task regs) :=
  let new := update m p input job state
  (new, wake state new pending)

/-- An absent job's equation is already satisfied. -/
def Stable (state : State m.value regs out) (pending : List (Task regs)) : Prop :=
  ∀ job, job ∉ pending → get (SCCP.transfer m p input state) job = get state job

def potential (state : State value regs out) (pending : List (Task regs)) : Nat :=
  FIFO.potential (height value regs out) (dataPorts regs).length.succ.succ state pending

def initial : List (Task regs) := [.control]

abbrev Run (value : Data → Type w) (regs : List (ValueSort Data)) (out : ValueSort Data) :=
  FIFO.Run (State value regs out) (Task regs)

def runSteps : Nat → State m.value regs out → List (Task regs) → Run m.value regs out :=
  FIFO.runSteps (step m p input)

/-- Start by marking entry. Strict state increases pay for new jobs. -/
def run : Run m.value regs out :=
  runSteps m p input (potential (⊥ : State m.value regs out) initial) ⊥ initial

def solve : State m.value regs out := (run m p input).state

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist
