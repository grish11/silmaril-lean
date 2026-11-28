module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Defs

/-! # Replay ranked placements on the current saved layout -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence

open Silmaril.MLIR.Arith (Width)

variable {Input : List Width} {saved carried result : Width}

/-- The caller supplies an original identity and the bound for its header
    walk. Physical cuts are discovered again on the current CFG. -/
structure Request where
  origin : Nat
  headerBudget : Nat
  deriving DecidableEq, Repr

structure Refusal where
  position : Nat
  request : Request
  deriving DecidableEq, Repr

structure Choice (source : Layout.Output Input saved carried result) (request : Request) where
  ranked : PreheaderSearch.Ranked source.2 request.origin
  checked : PreheaderSearch.rank? source.2 request.origin request.headerBudget = some ranked

/-- A suffix starts at the exact selected layout of the preceding ranker.
    Its dependent type includes any word added to the saved packet. -/
inductive Trace : Layout.Output Input saved carried result → List Request → Type where
  | done {source} : Trace source []
  | step {source request rest} (first : Choice source request)
      (tail : Trace first.ranked.selection.2 rest) : Trace source (request :: rest)

def Trace.output {source : Layout.Output Input saved carried result} {requests : List Request} :
    Trace source requests → Layout.Output Input saved carried result
  | .done => source
  | .step _ tail => tail.output

/-- Resolve, check and rank one live origin at a time. A refusal reports
    the failing request's position and carries no partial trace. -/
def run (source : Layout.Output Input saved carried result) (position : Nat) :
    (requests : List Request) → Except Refusal (Trace source requests)
  | [] => .ok .done
  | request :: rest =>
    match checked : PreheaderSearch.rank? source.2 request.origin request.headerBudget with
    | none => .error ⟨position, request⟩
    | some ranked =>
      (run ranked.selection.2 (position + 1) rest).map (.step ⟨ranked, checked⟩)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence
