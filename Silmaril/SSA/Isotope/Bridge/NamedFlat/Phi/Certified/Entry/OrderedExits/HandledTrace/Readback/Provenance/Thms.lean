module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Provenance.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Provenance.Alignment

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

universe u v
variable {Events : Type u → Type u} {F : Type v} {α β : Type (u + 1)}
  {blocks publicBlocks exits publicExits captures publicCaptures : Nat}
  {source : FiniteCFG F blocks exits captures} {target : FiniteCFG F publicBlocks publicExits publicCaptures}
  {left : Primitive Events F α} {right : Primitive Events F β}
  {leftEnv : Env α} {rightEnv : Env β} {atom : α → β}

/-- A structural seed evaluates purely to the value used in the public
capture packet contract. -/
theorem packet_term_tree (instr : Primitive Events F α) (env : Env α)
    (packet : Silmaril.SSA.LambdaRTL.Val (Fin captures)) :
    LambdaSSA.Semantics.Interaction.term instr env (packetTerm packet) = pure (packetValue env packet) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.Provenance.packet_tree
    instr env packet

/-- The exact source jump and public capture read generate the same
pending packet after encoding. -/
theorem Provenance.entry_eq (p : Provenance source target)
    (packet : rightEnv p.slot.val =
      valueCodec atom (packetValue leftEnv p.seed)) :
    Sum.map (resultCodec atom) (stateCodec p.count atom) <$> transfer left leftEnv blocks source.entry =
      transfer right rightEnv publicBlocks target.entry :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.Provenance.entry p packet

/-- Equal erased rows scoped to the packet alone give the same decoded
transfer at every reply. Neither row reads ambient capture slots. -/
theorem Provenance.step_eq (p : Provenance source target) (prim : PrimitivesAgree left right atom)
    (state : BlockInput α blocks) :
    Sum.map (resultCodec atom) (stateCodec p.count atom) <$> blockStep left source leftEnv state =
      blockStep right target rightEnv (stateCodec p.count atom state) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.Provenance.block p prim state

/-- Build the local alignment from exact row provenance and the selected
capture packet. The state codec keeps the written block order. -/
def Provenance.alignment (p : Provenance source target) (prim : PrimitivesAgree left right atom)
    (packet : rightEnv p.slot.val =
      valueCodec atom (packetValue leftEnv p.seed)) :
    Alignment source target left right leftEnv rightEnv atom :=
  ⟨stateCodec p.count atom, p.entry_eq packet, p.step_eq prim⟩

/-- The public entry's jump and argument slot come directly from its
accepted elaboration, using the actual label and capture lookups. -/
theorem packedEntry_erase_entry {G : Type} {signature : PrimitiveSignature G} {a b : Nat}
    {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
    {program : Program signature inputs outputs} {input : Fin a}
    (entry : Program.PackedEntry program input) (slot : Fin entry.count)
    (idx : Fin ((program.compile input).blocks.length + program.exits.length))
    (found : NamedFlat.first entry.captures ⟨0⟩ = some slot)
    (label : NamedFlat.labelIndex (program.compile input).blocks program.exits ⟨program.entry input⟩ = some idx) :
    entry.target.entry.erase = .br idx.val (.var slot.val) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.public_entry entry slot idx found label

/-- The checked public capture slot supplies exactly the encoded typed
packet passed to the public entry. -/
theorem packedEntry_capture_packet {G : Type} {signature : PrimitiveSignature G} {a b : Nat}
    {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
    {program : Program signature inputs outputs} {input : Fin a}
    (entry : Program.PackedEntry program input) (slot : Fin entry.count)
    (found : NamedFlat.first entry.captures ⟨0⟩ = some slot)
    (packet : Denote (inputs input)) (env : Env Atom) (agrees : entry.recordAgrees packet env) :
    env slot.val = PacketType.encode (inputs input) packet :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.capture_packet
    entry slot found packet env agrees

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
