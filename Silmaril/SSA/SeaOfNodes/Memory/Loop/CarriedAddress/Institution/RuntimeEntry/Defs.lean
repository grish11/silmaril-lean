module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Defs

/-! The typed entry domain for the emitted address-Phi runtime equations. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature} {args : List ValueSort} {cells : Nat}

/-- A raw tuple at the emitted boundary. Its types already enforce each
address's bound and one complete initialized heap of the same size. -/
abbrev RawEntry (args : List ValueSort) (cells : Nat) :=
  Tuple (WireVal cells) (Petri.carried args)

structure Entry (args : List ValueSort) (cells : Nat) where
  input : Tuple (Val cells) args
  heap : Heap cells

def Entry.model (entry : Entry P.args cells) : EntryModel P :=
  ⟨cells, entry.input⟩

def Entry.encode (entry : Entry args cells) : RawEntry args cells :=
  Petri.encodeArrival .entry entry.heap entry.input

/-- Split the existing memory encoding at its final heap port. -/
def decodePayload : {args : List ValueSort} → Tuple (WireVal cells) (carrier args) → Entry args cells
  | [], .cons heap .nil => ⟨.nil, heap⟩
  | _ :: _, .cons value rest =>
    let tail := decodePayload rest
    ⟨.cons value tail.input, tail.heap⟩

/-- The root must arrive from entry, encoded by zero. -/
def Admissible (raw : RawEntry args cells) : Prop :=
  (raw.get .head).down = 0

/-- Reject a feedback-coloured tuple at the root, even if its payload is typed. -/
def decode : RawEntry args cells → Option (Entry args cells)
  | .cons tag payload => if tag.down = 0 then some (decodePayload payload) else none

def Entry.reduct (h : P ⟶ Q) (entry : Entry Q.args cells) : Entry P.args cells :=
  ⟨(Memory.Diamond.Institution.reduct h entry.model).input, entry.heap⟩

/-- Pull back only the scalar ports. The raw occurrence and initialized
heap are retained. A feedback colour remains inadmissible. -/
def reindex (h : P ⟶ Q) : RawEntry Q.args cells → RawEntry P.args cells
  | .cons tag payload =>
    let pulled := (decodePayload payload).reduct h
    .cons tag (encodeInput pulled.heap pulled.input)

/-- The existing runtime program type at the typed entry and word/heap boundary. -/
abbrev Program (args : List ValueSort) :=
  RVSDG.NestedTheta.Institution.RuntimeObservation.Program ⟨ThetaOpcode⟩
    (Petri.carried args) (Threaded wordPorts)

def lowerProgram (graph : Graph args) : Program args :=
  ⟨_, Petri.lower graph⟩

noncomputable def observeProgram (program : Program args) (raw : RawEntry args cells) :
    Part (Tuple (WireVal cells) (Threaded wordPorts)) :=
  RVSDG.NestedTheta.Institution.RuntimeObservation.observe (P := ⟨ThetaOpcode⟩)
    (thetaRuntime cells) program.graph raw

/-- Evaluate the actual emitted nested graph with the existing runtime observer. -/
noncomputable def observe (graph : Graph args) (raw : RawEntry args cells) :
    Part (Tuple (WireVal cells) (Threaded wordPorts)) :=
  observeProgram (lowerProgram graph) raw

/-- Compare both complete partial results on every admissible raw entry at
this cell count. A finite result carries the word and entire final heap. -/
def Agrees (lhs rhs : Program args) (cells : Nat) : Prop :=
  ∀ raw : RawEntry args cells, Admissible raw → observeProgram lhs raw = observeProgram rhs raw

def Holds (e : Equation P) (cells : Nat) : Prop :=
  Agrees (lowerProgram e.lhs) (lowerProgram e.rhs) cells

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry
