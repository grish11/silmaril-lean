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

/-- Check one named capture, a packet-closed attached table and an exact
public re-elaboration. The entry must jump to an internal label with the
sole captured packet. The supplied types describe block packets and the
ordered exits after live-out attachment. -/
def construct [DecidableEq F] (signature : PrimitiveSignature F) (source : CFG V K F) (exits : List K)
    (fields : K → List V) (capture : V) (inputType : PacketType)
    (internal : Fin (LiveOut.attach fields source).blocks.length → PacketType)
    (outputs : Fin exits.length → PacketType) : Option (Constructed signature source exits fields capture inputType outputs) := do
  let attached := LiveOut.attach fields source
  if closed : ∀ i : Fin attached.blocks.length, attached.blocks[i.val].2.body.toRegion.fv ⊆
      {attached.blocks[i.val].2.param} then
    let names : Fin 1 → V := fun _ => capture
    match accepted : NamedFlat.elaborate attached exits names with
    | none => none
    | some flat => do
      let built ← Phi.Certified.Entry.OrderedExits.Readback.construct signature internal outputs flat
      if seed : built.provenance.seed = .var (0 : Fin 1) then
        if slot : built.provenance.slot.val = 0 then
          if captures : ∀ i, built.packed.captures i = ⟨0⟩ then
            if profile : internal built.start = inputType then
              let result : Constructed signature source exits fields capture (internal built.start) outputs :=
                ⟨built.program, built.packed,
                  ⟨1, names, built.provenance.exitCount,
                    Construction.packetClosed attached closed,
                    attached.blocks.length, rfl, flat, (NamedFlat.elaborateAt_eq _ exits names).trans accepted,
                    Construction.erase_eq built.provenance seed slot⟩,
                  fun _ => rfl, captures⟩
              some (profile ▸ result)
            else none
          else none
        else none
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

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
