module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.TwoRequests.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.TwoRequests.Execution

/-! # Weak execution of the checked two-request split -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.TwoRequests

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)

universe u w

/-- The silent hop restores the packet and first reply at their original
indices. All primitive continuations and the ordered exit are preserved. -/
theorem Emitted.preserves_run {E : Type w → Type w} {F : Type} {α : Type u} {exits captures : Nat}
    {source : FiniteCFG F 1 exits captures} {s : Shape source} (emitted : Emitted s)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env emitted.code.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.TwoRequests.preserves_run
    instr env s emitted

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Atom PacketType PrimitiveSignature Program)
open Silmaril.Elgot.ITree.Finite (Event)

/-- A successful public construction on the split rows identifies the
original run with the actual packed public dispatcher. Exact row provenance
is for the split table, and the supplied primitive and capture codecs connect
the two runtime environments. -/
theorem Emitted.public_run {F : Type} {α : Type 1} {exits captures : Nat}
    {source : FiniteCFG F 1 exits captures} {s : Shape source} (emitted : Emitted s)
    {signature : PrimitiveSignature F} {packet : PacketType} {external : Fin exits → PacketType}
    (built : Constructed signature (packets signature packet s) external emitted.code)
    {instr : Primitive (Event signature.Request signature.Reply) F α}
    (env : Env α) (publicAmbient publicRecord : Env Atom) (atom : α → Atom)
    (prim : PrimitivesAgree instr signature.primitive atom)
    (capture : publicRecord built.provenance.slot.val =
      valueCodec atom (packetValue env built.provenance.seed)) :
    resultCodec atom <$> (region instr env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      built.packed.observe publicAmbient publicRecord := by
  let _ := signature.typing
  rw [emitted.preserves_run instr env, Program.PackedEntry.observe,
    NamedFlat.Capture.packed_context_tree]
  exact (built.provenance.alignment prim capture).packed

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.TwoRequests
