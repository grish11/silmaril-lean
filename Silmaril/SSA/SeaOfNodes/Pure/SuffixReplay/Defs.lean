module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Defs

/-! Replay nominated word-add edits and unused-producer deletions on a
pure suffix with a word return and a typed packet of additional uses. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay

open Diamond (Dataflow Ty Val ValueSort dataPorts)
open ConstantFold
open ConstantFold.RightSpine (WordWire)
open GVN.Elimination (Rewrite Routing)
open GVN.Cyclic.Deletion (Route)
open SubZero (model word wordPort)
open RVSDG (Tuple Wires extend)

variable {inputs : List (ValueSort Unit)} {ports : List (Ty Unit)}
variable {original : List (List (Ty Unit))}

/-- The first outgoing wire is the word return. The rest are all additional
outgoing uses in this scope, in caller-supplied order. -/
structure Block (inputs : List (ValueSort Unit)) (ports : List (Ty Unit)) where
  sigs : List (List (Ty Unit))
  flow : Dataflow SubZero.Opcode (dataPorts inputs) [] sigs
  packet : Wires (dataPorts inputs) (extend [] sigs) (wordPort :: ports)

def Block.program (block : Block inputs ports) : Program SubZero.Opcode inputs word where
  dataflow := block.flow
  result := block.packet.get .head

inductive Action where
  | idealize
  | deleteUnused
  deriving DecidableEq, Repr

/-- Every nomination names a typed wire in the initial table. It follows
value redirection across edits and becomes stale if its route is deleted. -/
structure Request (inputs : List (ValueSort Unit)) (original : List (List (Ty Unit))) where
  action : Action
  wire : WordWire (dataPorts inputs) (extend [] original)

inductive Reason where
  | stale
  | nomination (reason : AddIdealize.Replay.Stop)
  | idealize (reason : AddIdealize.Refusal)
  | noEdit
  | liveUse
  deriving DecidableEq, Repr

structure Failure where
  index : Nat
  reason : Reason
  deriving DecidableEq, Repr

structure State (inputs : List (ValueSort Unit)) (ports : List (Ty Unit))
    (original : List (List (Ty Unit))) where
  block : Block inputs ports
  route : Route (dataPorts inputs) (extend [] original) (extend [] block.sigs)

/-- The partial route preserves mapped reads, and routes the entire original
packet to the current packet. -/
def Agrees (before : Block inputs ports) (state : State inputs ports before.sigs)
    (entry : Tuple (Val model.value) (dataPorts inputs)) : Prop :=
  Route.Agrees state.route model entry (before.flow.eval model entry PUnit.unit)
    (state.block.flow.eval model entry PUnit.unit) ∧
    Route.wires? state.route before.packet = some state.block.packet

def initial (block : Block inputs ports) : State inputs ports block.sigs :=
  ⟨block, fun wire => some wire⟩

def State.compose (first : State inputs ports original) (next : State inputs ports first.block.sigs) :
    State inputs ports original :=
  ⟨next.block, fun wire => (first.route wire).bind next.route⟩

def fromRewrite (block : Block inputs ports)
    (edit : Rewrite SubZero.Opcode (dataPorts inputs) [] block.sigs) : State inputs ports block.sigs :=
  ⟨⟨edit.sigs', edit.flow, Routing.wires edit.route block.packet⟩, fun wire => some (edit.route wire)⟩

/-- Resolve a wire in the current table and require one accepted edit.
This profile supplies no source IDs. Rules requiring them can refuse. -/
def step (block : Block inputs ports) (action : Action)
    (wire : WordWire (dataPorts inputs) (extend [] block.sigs)) : Except Reason (State inputs ports block.sigs) :=
  match AddIdealize.Replay.nominate block.program wire with
  | .error reason => .error (.nomination reason)
  | .ok candidate =>
    match action with
    | .idealize =>
      match AddIdealize.step ⟨fun _ => none⟩ block.program candidate with
      | .error reason => .error (.idealize reason)
      | .ok none => .error .noEdit
      | .ok (some applied) => .ok (fromRewrite block applied.rewrite)
    | .deleteUnused =>
      match Deletion.delete? candidate block.packet with
      | none => .error .liveUse
      | some deleted => .ok ⟨⟨deleted.erasure.sigs', deleted.erasure.flow, deleted.outputs⟩, deleted.erasure.route⟩

def advance (state : State inputs ports original) (request : Request inputs original) :
    Except Reason (State inputs ports original) :=
  match state.route request.wire with
  | none => .error .stale
  | some wire => (step state.block request.action wire).map state.compose

/-- The finite request list bounds the replay. Failure includes the first
failing index and carries no prefix graph. -/
def runFrom (state : State inputs ports original) (index : Nat) :
    List (Request inputs original) → Except Failure (State inputs ports original)
  | [] => .ok state
  | request :: rest =>
    match advance state request with
    | .error reason => .error ⟨index, reason⟩
    | .ok next => runFrom next (index + 1) rest

def run (block : Block inputs ports) (requests : List (Request inputs block.sigs)) :
    Except Failure (State inputs ports block.sigs) :=
  runFrom (initial block) 0 requests

end Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay
