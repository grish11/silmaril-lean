module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Defs
public import Mathlib.Logic.Function.Basic

/-! Typed destination jobs for the Φ equation of the cyclic SCCP worklist. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Origin Tuple Wires extend)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {value : Data → Type w}

abbrev Job (carried : List (ValueSort Data)) := Fin (dataPorts carried).length

def wireAt {args : List (Ty Data)} {past : List (List (Ty Data))} :
    {ports : List (Ty Data)} → Wires args past ports →
      (i : Fin ports.length) → Origin args past ports[i]
  | [], .nil, i => i.elim0
  | _ :: _, .cons wire tail, i => Fin.cases wire (wireAt tail) i

/-- A direct wire watches its one typed fact. A producer wire conservatively
watches the old bank and uses the existing shared evaluator when popped. -/
abbrev FeedbackInput (value : Data → Type w) (carried : List (ValueSort Data)) (job : Job carried) :=
  Sum (Fact value (dataPorts carried)[job]) (BankFacts value (dataPorts carried))

abbrev Watched (value : Data → Type w) (carried : List (ValueSort Data)) (job : Job carried) :=
  Bool × Option (FeedbackInput value carried job)

variable (m : Model.{u, v, w} Op) [eqBank : BankDecidableEq m.value (dataPorts carried)]
variable (g : Graph Op inputs carried entrySigs headerSigs out)
variable (input : Tuple (Fact m.value) (dataPorts inputs))

/-- The backedge mark gates all feedback dependencies. Captured argument
facts are immutable during the worklist, so reads of them never wake a job. -/
def dependencies (state : State m.value carried out) (job : Job carried) : Watched m.value carried job :=
  (decide (incomingIndex .entry ∈ state.1),
    if incomingIndex .backedge ∈ state.1 then
      some (match wireAt (g.phiInputs .backedge) job with
        | .arg port => .inl ((appendTuple (bankTuple state.2.1) input).get port)
        | .output _ _ => .inr state.2.1)
    else none)

def evaluate (job : Job carried) (watched : Watched m.value carried job) :
    Fact m.value (dataPorts carried)[job] :=
  let entry := if watched.1 then entryFacts m g input job else ⊥
  let feedback := match watched.2 with
    | none => ⊥
    | some (.inl fact) => fact
    | some (.inr old) => (headerFacts m g input old).feedback job
  @Flat.join _ (eqBank.atPort job) entry feedback

/-- Publish one destination, using its own field type. -/
def write (state : State value carried out) (job : Job carried)
    (fact : Fact value (dataPorts carried)[job]) : State value carried out :=
  (state.1, Function.update state.2.1 job fact, state.2.2)

def update (job : Job carried) (state : State m.value carried out) : State m.value carried out :=
  write state job (evaluate m g input job (dependencies m g input state job))

instance (job : Job carried) : DecidableEq (Watched m.value carried job) :=
  let _ : ∀ i : Job carried, DecidableEq (Fact m.value (dataPorts carried)[i]) :=
    fun i => @Semantics.Dataflow.instDecidableEqFlat _ (eqBank.atPort i)
  let _ : DecidableEq (BankFacts m.value (dataPorts carried)) := Fintype.decidablePiFintype
  inferInstanceAs (DecidableEq (Bool × Option (Sum (Fact m.value (dataPorts carried)[job])
    (BankFacts m.value (dataPorts carried)))))

/-- Append only changed destinations that are absent from the pending queue. -/
def wake (old new : State m.value carried out) (pending : List (Job carried)) : List (Job carried) :=
  FIFO.wake (List.finRange (dataPorts carried).length)
    (fun job => decide (dependencies m g input new job ≠ dependencies m g input old job)) pending

/-- Pop one typed Φ job. Control and result jobs belong to the enclosing scheduler. -/
def step (job : Job carried) (state : State m.value carried out) (pending : List (Job carried)) :
    State m.value carried out × List (Job carried) :=
  let new := update m g input job state
  (new, wake m g input state new pending)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi
