module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA.Semantics (Env)
open LambdaSSA (FiniteCFG)

namespace Construction

open Phi.Certified.Entry.OrderedExits.Readback (Provenance)

theorem packetClosed {V K : Type 1} [DecidableEq V] {F : Type} (graph : CFG V K F)
    (closed : ∀ i : Fin graph.blocks.length, graph.blocks[i.val].2.body.toRegion.fv ⊆
      {graph.blocks[i.val].2.param}) : RoundTrip.PacketClosed graph :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Construction.packetClosed graph closed

theorem erase_eq {F : Type} {blocks publicBlocks exits publicExits publicCaptures : Nat}
    {flat : FiniteCFG F blocks exits 1} {publicCode : FiniteCFG F publicBlocks publicExits publicCaptures}
    (provenance : Provenance flat publicCode) (seed : provenance.seed = .var (0 : Fin 1))
    (slot : provenance.slot.val = 0) : flat.erase = publicCode.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Construction.erase_eq provenance seed slot

end Construction

open Phi.Certified.Entry.OrderedExits.Readback (Provenance packetValue)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source : CFG V K F} {exits : List K} {fields : K → List V}
  {capture : V} {inputType : PacketType} {outputs : Fin exits.length → PacketType}

/-- One public entry with its checked packed code, exact original RTL
readback, and the registers used to supply its packet on both sides. -/
structure Constructed (signature : PrimitiveSignature F) (source : CFG V K F) (exits : List K)
    (fields : K → List V) (capture : V) (inputType : PacketType) (outputs : Fin exits.length → PacketType) where
  program : Program signature (fun _ : Fin 1 => inputType) outputs
  entry : Program.PackedEntry program 0
  readback : Readback entry source exits fields
  namedCaptures : ∀ i, readback.captures i = capture
  publicCaptures : ∀ i, entry.captures i = ⟨0⟩

/-- Literal named readback and exact agreement at every internal row.
Provenance checks both entries against the same internal label and
records the source expression and the public packet slot separately. -/
structure Seeded (signature : PrimitiveSignature F) (source : CFG V K F) (exits : List K)
    (fields : K → List V) (capture : V) (inputType : PacketType) (outputs : Fin exits.length → PacketType) where
  program : Program signature (fun _ : Fin 1 => inputType) outputs
  entry : Program.PackedEntry program 0
  closed : RoundTrip.PacketClosed (LiveOut.attach fields source)
  flat : FiniteCFG F (LiveOut.attach fields source).blocks.length exits.length 1
  accepted : NamedFlat.elaborate (LiveOut.attach fields source) exits (fun _ : Fin 1 => capture) = some flat
  provenance : Provenance flat entry.target
  publicCaptures : ∀ i, entry.captures i = ⟨0⟩

/-- Check a purely structural constant or a literal capture read at the
entry jump. The supplied types describe the attached blocks and exits.
The packet at a concrete store is checked separately by `Seeded.checkSeed`. -/
def constructSeeded [DecidableEq F] (signature : PrimitiveSignature F) (source : CFG V K F) (exits : List K)
    (fields : K → List V) (capture : V) (inputType : PacketType)
    (internal : Fin (LiveOut.attach fields source).blocks.length → PacketType)
    (outputs : Fin exits.length → PacketType) : Option (Seeded signature source exits fields capture inputType outputs) := do
  let attached := LiveOut.attach fields source
  if closed : ∀ i : Fin attached.blocks.length, attached.blocks[i.val].2.body.toRegion.fv ⊆
      {attached.blocks[i.val].2.param} then
    let names : Fin 1 → V := fun _ => capture
    match accepted : NamedFlat.elaborate attached exits names with
    | none => none
    | some flat => do
      let built ← Phi.Certified.Entry.OrderedExits.Readback.construct signature internal outputs flat
      let supported := match built.provenance.seed with
        | .var _ => true
        | seed => decide (seed.fv = ∅)
      if supported then
        if captures : ∀ i, built.packed.captures i = ⟨0⟩ then
          if profile : internal built.start = inputType then
            let result : Seeded signature source exits fields capture (internal built.start) outputs :=
              ⟨built.program, built.packed, Construction.packetClosed attached closed, flat, accepted,
                built.provenance, captures⟩
            some (profile ▸ result)
          else none
        else none
      else none
  else none

/-- The original literal-entry constructor also checks exact erasure of the
entry. Its whole-table readback still requires the same written slot-zero
read on both sides. -/
def construct [DecidableEq F] (signature : PrimitiveSignature F) (source : CFG V K F) (exits : List K)
    (fields : K → List V) (capture : V) (inputType : PacketType)
    (internal : Fin (LiveOut.attach fields source).blocks.length → PacketType)
    (outputs : Fin exits.length → PacketType) : Option (Constructed signature source exits fields capture inputType outputs) := do
  let built ← constructSeeded signature source exits fields capture inputType internal outputs
  if seed : built.provenance.seed = .var (0 : Fin 1) then
    if slot : built.provenance.slot.val = 0 then
      let names : Fin 1 → V := fun _ => capture
      some ⟨built.program, built.entry,
        ⟨1, names, built.provenance.exitCount, built.closed, _, rfl, built.flat,
          (NamedFlat.elaborateAt_eq _ exits names).trans built.accepted,
          Construction.erase_eq built.provenance seed slot⟩,
        fun _ => rfl, built.publicCaptures⟩
    else none
  else none

/-- Fill the checked capture record with the exact encoding of the supplied
public packet. Only captured positions can be read by the dispatcher. -/
def packetRecord (packet : Denote inputType) : Env Atom :=
  fun _ => PacketType.encode inputType packet

/-- A runtime check connects a caller-supplied initial store to the packet.
The construction of the code alone does not constrain initial values. -/
def checkCapture (capture : V)
    (initial : V → Value Atom) (packet : Denote inputType) : Bool :=
  decide (initial capture = packetRecord packet 0)

def Seeded.evalSeed (built : Seeded signature source exits fields capture inputType outputs)
    (initial : V → Value Atom) : Value Atom :=
  packetValue (fun _ => initial capture) built.provenance.seed

/-- Compare the source entry's evaluated seed in the actual initial store
with the encoded public packet. The provenance fixes their common label. -/
def Seeded.checkSeed (built : Seeded signature source exits fields capture inputType outputs)
    (initial : V → Value Atom) (packet : Denote inputType) : Bool :=
  decide (built.evalSeed initial = packetRecord packet built.provenance.slot.val)

/-- Recover this entry's typed packet and check its exact encoding against
the evaluated seed. -/
def decodeSeed? (ty : PacketType) (seed : Value Atom) : Option (Denote ty) := do
  let packet ← PacketType.decode ty seed
  if seed = PacketType.encode ty packet then some packet else none

def Seeded.seed? (built : Seeded signature source exits fields capture inputType outputs)
    (initial : V → Value Atom) : Option (Denote inputType) :=
  decodeSeed? inputType (built.evalSeed initial)

/-- Evaluate both seeds at one initial store. Failure to decode either
packet leaves the comparison undefined. -/
def Seeded.refinementFromStore? [DecidableEq F] {target : CFG V K F} {rightCapture : V} {rightType : PacketType}
    (left : Seeded signature source exits fields capture inputType outputs)
    (right : Seeded signature target exits fields rightCapture rightType outputs) (initial : V → Value Atom) :
    Option Bool := do
  let leftPacket ← left.seed? initial
  let rightPacket ← right.seed? initial
  return left.program.refinementBetween? right.program 0 leftPacket 0 rightPacket

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
