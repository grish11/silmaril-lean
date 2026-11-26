module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Infer.Defs

/-! # Exact packet-local admission of the materialized flat table -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v
variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}

local notation "ports" => numberedInterface context exits external

/-- The literal readback and actual ranked reversion of the emitted table. -/
structure CompiledFlat (code : FiniteCFG P.Instr blocks exits.length n) where
  lowered : Lowered ports fields code
  admission : Admission lowered
  ranked : admission.acyclicCheck = true

/-- The common post-emission gates of the witnessed and flat entry paths. -/
def checkRanked [DecidableEq κ] {code : FiniteCFG P.Instr blocks exits.length n}
    (lowered : Lowered ports fields code) (R : Fin blocks → Ty κ) :
    Option (CompiledFlat (context := context) (external := external) (fields := fields) code) :=
  if checked : Straight.packetLocalChecks lowered R = true then
    let admission := admit lowered R checked
    if ranked : admission.acyclicCheck = true then some ⟨lowered, admission, ranked⟩ else none
  else none

/-- Carry a caller-supplied layout, then run the ordinary named emitter,
literal live-out readback, typed reversion, and reachable-rank check. -/
def compileFlatCarry? [DecidableEq κ] [DecidableEq P.Instr]
    (code : FiniteCFG P.Instr blocks exits.length n) (R : Fin blocks → Ty κ)
    (slots : List (Fin n)) (registers : Registers Register) (labels : Fin blocks → K) :
    Option (CompiledFlat (context := context) (external := external) (fields := fields) (Capture.Carry.graphList code slots)) := do
  let lowered ← lowerChecked ports fields registers labels (Capture.Carry.graphList code slots)
  checkRanked lowered (Capture.Carry.packetTypesList R context slots)

/-- Infer slots from the written rows using the same analysis as the
witnessed LetCase entry point. The caller supplies label and register names. -/
def compileFlatInferred? [DecidableEq κ] [DecidableEq P.Instr]
    (code : FiniteCFG P.Instr blocks exits.length n) (R : Fin blocks → Ty κ)
    (registers : Registers Register) (labels : Fin blocks → K) :
    Option (CompiledFlat (context := context) (external := external) (fields := fields) (Capture.Carry.graphList code (Capture.Carry.inferSlots code))) :=
  compileFlatCarry? (context := context) (external := external) (fields := fields) code R (Capture.Carry.inferSlots code) registers labels

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
