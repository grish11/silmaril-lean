module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Defs

/-! # Recover the first actual exit occurrence from bounded typed CF -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Frame Terminator)
open Loop.MLIR.CF (evalOp)

variable {Input bank full Γ Δ extra : List Width} {saved carried result : Width}

/-- Expose the branch slot alongside the ordinary CF terminator result.
The guard is read in the same terminal environment as CF execution. -/
def select (term : Terminator (ExitLabel bank full) Δ Γ) (env : Env Γ) :
    (EdgeSlot × Frame (ExitLabel bank full)) ⊕ Env Δ :=
  match term with
  | .br edge => .inl (.jump, edge.eval env)
  | .condBr guard yes no =>
    if (env.get guard).getLsbD 0 then .inl (.onTrue, yes.eval env) else .inl (.onFalse, no.eval env)
  | .ret values => .inr (values.eval env)

def branches (term : Terminator (ExitLabel bank full) Δ Γ) : Bool :=
  match term with
  | .ret _ => false
  | _ => true

variable (cfg : TargetCfg Input saved carried result extra full)

def entryPacket? (input : Env Input) : Option (Env (SavedBank saved carried extra)) :=
  match cfg.entry.eval evalOp (fun term env => term.eval env) input with
  | .inl ⟨.header, packet⟩ => some packet
  | _ => none

/-- Check that entry actually reaches the header and that the header has
a branch terminator. Either header successor may reach the exit. -/
def admitted (input : Env Input) : Bool :=
  (entryPacket? cfg input).isSome && branches (terminal (cfg.block .header)).2

/-- The last header environment, taken slot, and packet before entering
the exit. Remaining fuel is measured in CF blocks. -/
structure Arrival (Input bank full : List Width) where
  feedbacks : Nat
  slot : EdgeSlot
  env : Env (bank ++ Input)
  packet : Env full
  remaining : Nat

def Arrival.project (arrival : Arrival Input bank full) (p : Projection full) :
    Arrival Input bank p.types :=
  { arrival with packet := p.values arrival.packet }

def Arrival.bump (arrival : Arrival Input bank full) : Arrival Input bank full :=
  { arrival with feedbacks := arrival.feedbacks + 1 }

/-- Consume one block per step and stop at the first taken exit edge.
Only a taken feedback edge advances the feedback count. -/
def firstFrom? (input : Env Input) :
    Nat → Env (SavedBank saved carried extra ++ Input) → Option (Arrival Input (SavedBank saved carried extra) full)
  | 0, _ => none
  | fuel + 1, env =>
    match (cfg.block .header).eval evalOp select env with
    | .inl (slot, ⟨.exit, packet⟩) => some ⟨0, slot, env, packet, fuel⟩
    | .inl (_, ⟨.header, packet⟩) => (firstFrom? input fuel (packet.append input)).map Arrival.bump
    | .inr _ => none

/-- Start at the actual entry and spend its block fuel before walking the
header. A recovered arrival can still have zero fuel left for the exit. -/
def firstExit? (input : Env Input) : Nat → Option (Arrival Input (SavedBank saved carried extra) full)
  | 0 => none
  | fuel + 1 => (entryPacket? cfg input).bind (fun packet => firstFrom? cfg input fuel (packet.append input))

variable {cfg}

/-- A successful run identifies the same first exit on the full and compact
CFGs, with an admitted positional Φ row on the compact artifact. -/
structure Recovery (emission : Emission cfg) (input : Env Input) (fuel : Nat) (output : Env [result]) where
  arrival : Arrival Input (SavedBank saved carried extra) full
  fullFound : firstExit? cfg input fuel = some arrival
  compactFound : firstExit? emission.cfg input fuel = some (arrival.project emission.projection)
  rowPresent : (operandsAt? emission.cfg (.header, arrival.slot)).isSome
  fullPacket : packetAt? cfg (.header, arrival.slot) arrival.env = some arrival.packet
  compactPacket : packetAt? emission.cfg (.header, arrival.slot) arrival.env =
    some (emission.projection.values arrival.packet)
  latch : latchAt? emission.cfg (.header, arrival.slot) arrival.env =
    some (pack (emission.projection.values arrival.packet))
  exitReturns : emission.cfg.runFrom evalOp arrival.remaining input
    ⟨.exit, emission.projection.values arrival.packet⟩ = some output
  fullReturns : cfg.run evalOp fuel input = some output

def Recovery.row {emission : Emission cfg} {input : Env Input} {fuel : Nat} {output : Env [result]}
    (recovered : Recovery emission input fuel output) : Incoming emission.cfg :=
  ⟨(.header, recovered.arrival.slot), recovered.rowPresent⟩

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run
