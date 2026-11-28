module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Defs

/-! # Finite replay with a typed physical saved-prefix layout -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Terminator)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.SCF (For)
open AfterReorder.Second (Candidate checkPrefixCut)
open AfterReorder.Second.Emit (liftCode)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra : List Width} {saved carried result : Width}

/-- The append reference tracks logical slots and surviving origins. Its
    labeled blocks consume the same packets as the physical entry. -/
structure State (Input : List Width) (saved carried result : Width) (extra : List Width) where
  reference : Step.State Input saved carried result extra
  physical : List Width
  leading : Saved.Prefix Input physical
  tail : Block TargetOp (Label saved carried result extra) physical [result]
  toPhysical : Rename ((extra ++ [saved]) ++ Input) physical

def State.cfg (state : State Input saved carried result extra) :
    Cfg TargetOp (Label saved carried result extra) Input [result] :=
  { state.reference.cfg with entry := state.leading.wrap state.tail }

/-- Check the actual prefix of a canonical append state and start with
    its identity map. -/
def initial? (reference : Step.State Input saved carried result extra) :
    Option (State Input saved carried result extra) := do
  let (leading, tail) ← Saved.splitPrefix? reference.cfg.entry (extra ++ [saved])
  pure ⟨reference, _, leading, tail, fun ref => ref⟩

def State.savedCount (state : State Input saved carried result extra) : Nat :=
  state.physical.length - Input.length

/-- Look up a saved original identity in the logical packet, then locate its
    real physical definition. The physical scope is newest first. -/
def State.physicalSlot? (state : State Input saved carried result extra) (origin : Nat) : Option Nat :=
  (state.reference.slots.find? origin).map fun ⟨_, ref⟩ =>
    (state.toPhysical (Saved.prefixRef Input ref)).index

/-- Physical references count backwards from the end of the saved prefix.
    The immutable input suffix is available at cut zero. -/
def physicalSites {Γ : List Width} (count : Nat) : {args : List Width} → Operands Γ args →
    List (Point (Label saved carried result extra))
  | _, .nil => []
  | _, .cons ref rest => ⟨none, count - ref.index⟩ :: physicalSites count rest

def State.physicalOperands (state : State Input saved carried result extra)
    (candidate : Candidate Input saved carried result extra) : Operands state.physical candidate.args :=
  For.renameOperands state.toPhysical candidate.inputs

/-- Remap defining sites while retaining the current ordinary and Φ uses. -/
def State.atLayout (state : State Input saved carried result extra)
    (candidate : Candidate Input saved carried result extra) : Candidate Input saved carried result extra :=
  { candidate with operands := physicalSites state.savedCount (state.physicalOperands candidate) }

structure Move (state : State Input saved carried result extra) where
  append : Step.Emission Input saved carried result extra
  splice : Saved.Prefix.Insertion Input state.physical append.candidate.width

/-- Old logical references go through the previous map and then the splice.
    The new logical head names the newly inserted physical binding. -/
def Move.next {state : State Input saved carried result extra} (moved : Move state) :
    State Input saved carried result (moved.append.candidate.width :: extra) :=
  ⟨moved.append.next, _, moved.splice.leading,
    liftCode moved.splice.previous moved.splice.inserted state.tail,
    replaceBinding (fun ref => moved.splice.previous (state.toPhysical ref)) moved.splice.inserted⟩

/-- Recheck each request on the current physical CFG, then emit the
    insertion with typed operands in that scope. -/
def emit? (state : State Input saved carried result extra) (request : Nomination) : Option (Move state) := do
  let .ok append := Step.emit state.reference { request with cut := (extra ++ [saved]).length } | none
  if checkPrefixCut state.cfg (state.atLayout append.candidate) request.cut then
    let splice ← state.leading.insert? append.candidate.op (state.savedCount - request.cut)
      (state.physicalOperands append.candidate)
    pure ⟨append, splice⟩
  else none

abbrev Output (Input : List Width) (saved carried result : Width) :=
  (extra : List Width) × State Input saved carried result extra

/-- Replay the whole list, returning no CFG on refusal. Cuts belong to the
    physical prefix at each step and origins retain their original identities. -/
def run : {extra : List Width} → State Input saved carried result extra → Nat →
    List Nomination → Except Refusal (Output Input saved carried result)
  | extra, state, _, [] => .ok ⟨extra, state⟩
  | _, state, position, request :: rest =>
    match emit? state request with
    | none => .error (.nomination position request .rejected)
    | some moved => run moved.next (position + 1) rest

/-- Translate a physical plan into the checked reference's append coordinates. -/
def appendPlan : Nat → List Nomination → List Nomination
  | _, [] => []
  | count, request :: rest => { request with cut := count } :: appendPlan (count + 1) rest

/-- Physical references read the actual reference-prefix values. The entry
    has the same successor slots and packet as the reference for every input.
    All labeled blocks are shared by the two CFGs by construction. -/
structure Invariant (state : State Input saved carried result extra) : Prop where
  scopeSize : state.physical.length = ((extra ++ [saved]) ++ Input).length
  prefixAgreement : ∃ leading tail,
    Saved.splitPrefix? state.reference.cfg.entry (extra ++ [saved]) = some (leading, tail) ∧
    ∀ (input : Env Input) {w} (ref : Var _ w),
      (state.leading.eval input).get (state.toPhysical ref) = (leading.eval input).get ref
  targets : (shape state.cfg none).target = (shape state.reference.cfg none).target
  entry : ∀ input : Env Input,
    state.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      state.reference.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout
