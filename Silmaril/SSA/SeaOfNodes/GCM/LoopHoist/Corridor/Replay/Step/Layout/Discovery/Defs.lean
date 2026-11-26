module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Defs

/-! # Bounded discovery on the actual saved-prefix layout -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery

open Silmaril.MLIR.Arith (Width)

variable {Input extra : List Width} {saved carried result : Width}

def tryMove (state : Layout.State Input saved carried result extra) (request : Nomination) :
    Except Reason (Layout.Move state) :=
  match Layout.emit? state request with
  | some moved => .ok moved
  | none => .error .rejected

/-- Try physical cuts in ascending order. At each cut, scan the surviving
    identities in current header order and keep the first checked edit. -/
def choose? (state : Layout.State Input saved carried result extra) :
    Option (Nomination × Layout.Move state) :=
  (List.range (state.savedCount + 1)).findSome? fun cut =>
    Replay.Discovery.choose? state.reference.origins cut (tryMove state)

inductive Stop where
  | fixedPoint
  | bound
  deriving DecidableEq, Repr

structure Plan (Input : List Width) (saved carried result : Width) where
  requests : List Nomination
  output : Layout.Output Input saved carried result
  stop : Stop

/-- Rescan the emitted layout after each edit. At the bound, check whether
    a next move exists so that exhaustion and budget truncation are distinct. -/
def collect : {extra : List Width} → Layout.State Input saved carried result extra → Nat →
    Plan Input saved carried result
  | extra, state, 0 => ⟨[], ⟨extra, state⟩, if (choose? state).isNone then .fixedPoint else .bound⟩
  | extra, state, budget + 1 =>
    match choose? state with
    | none => ⟨[], ⟨extra, state⟩, .fixedPoint⟩
    | some (request, moved) =>
      let rest := collect moved.next budget
      ⟨request :: rest.requests, rest.output, rest.stop⟩

/-- A fixed point excludes every request accepted by the represented
    transition. A budget stop has a checked next move. -/
def Plan.stopSpec (plan : Plan Input saved carried result) (budget : Nat) : Prop :=
  match plan.stop with
  | .fixedPoint => ∀ request, Layout.emit? plan.output.2 request = none
  | .bound => plan.requests.length = budget ∧ ∃ request moved, Layout.emit? plan.output.2 request = some moved

inductive Unsupported where
  | prefix
  | shape
  deriving DecidableEq, Repr

/-- Check the entry jump, the two header occurrences and the return
    consumed by the emitter, together with its live origin inventory. -/
def supported? (state : Layout.State Input saved carried result extra) : Bool :=
  let header := shape state.cfg AfterReorder.Second.savedHeader
  let inventory := decide (state.reference.origins.length = header.bindings ∧ state.reference.origins.Nodup)
  match (shape state.cfg none).target .jump, header.target .onTrue, header.target .onFalse, state.cfg.block .exit with
  | some ⟨_, .header⟩, some ⟨_, .header⟩, some ⟨_, .exit⟩, .terminator (.ret _)
  | some ⟨_, .header⟩, some ⟨_, .exit⟩, some ⟨_, .header⟩, .terminator (.ret _) => inventory
  | _, _, _, _ => false

/-- Opt into physical discovery from an existing canonical saved state.
    Unchecked prefixes and unsupported shapes report refusal before the search. -/
def discover (reference : Step.State Input saved carried result extra) (budget : Nat) :
    Except Unsupported (Plan Input saved carried result) := do
  let some state := Layout.initial? reference | .error .prefix
  if supported? state then .ok (collect state budget) else .error .shape

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery
