module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Defs

/-! # Checked sequences of distinct header placements -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Loop.MLIR.CF (Program TargetOp lower)
open Earlier (Operation operations)
open Pair (Request)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- Follow the emitter's removal and reinsertion on any list in binding order. -/
def relocate {α : Type _} (request : Request) (chosen : α) (bindings : List α) : List α :=
  (bindings.eraseIdx request.binding).insertIdx request.insertion chosen

structure State (Input : List Width) (carried result : Width) where
  cfg : Cfg TargetOp (SourceLabel carried result) Input [result]
  /-- Each current position names its original binding index. -/
  origins : List Nat
  /-- Original identities already scheduled, newest first. -/
  moved : List Nat

def initial (cfg : Cfg TargetOp (SourceLabel carried result) Input [result]) :
    State Input carried result :=
  ⟨cfg, List.range (operations (cfg.block .header)).length, []⟩

/-- Every request uses the current binding index and current pre-removal cut.
A successful checked move carries the selected original identity along. -/
def step? (state : State Input carried result) (request : Request) :
    Option (State Input carried result) := do
  let origin ← state.origins[request.binding]?
  if origin ∈ state.moved then none
  else
    let cfg ← Pair.move? state.cfg request
    pure ⟨cfg, relocate request origin state.origins, origin :: state.moved⟩

/-- Return the final state only when all requests succeed. -/
def run? (state : State Input carried result) :
    List Request → Option (State Input carried result)
  | [] => some state
  | request :: rest => (step? state request).bind fun next => run? next rest

def schedule? (g : Program Input carried result entrySigs headerSigs)
    (requests : List Request) : Option (Cfg TargetOp (SourceLabel carried result) Input [result]) :=
  (run? (initial (lower g)) requests).map State.cfg

/-- Origins form a permutation of the source indices and agree with the
actual typed-operation order. The moved identities are distinct. -/
def Tracked (source : List Operation) (state : State Input carried result) : Prop :=
  state.origins.Perm (List.range source.length) ∧
  state.origins.map (fun origin => source[origin]?) = (operations (state.cfg.block .header)).map some ∧
  state.moved.Nodup

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence
