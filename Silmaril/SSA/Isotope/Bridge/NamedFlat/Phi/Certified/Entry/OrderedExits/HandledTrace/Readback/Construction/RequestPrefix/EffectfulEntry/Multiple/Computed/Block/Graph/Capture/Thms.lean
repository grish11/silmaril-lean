module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.CapturePassing

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom PacketType PrimitiveSignature)
open NamedFlat.Capture.Carry (inferSlots packValue)

universe u w
variable {F : Type} {E : Type w → Type w} {α : Type u} {blocks exits captures : Nat}
  {sig : PrimitiveSignature F} {context : BoundCtx PacketType captures}
  {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
  {source : FiniteCFG F blocks exits captures}

/-- The carried packets preserve the original ambient run, including
backedges, outward payloads, and any nonterminating weak tree. -/
theorem prepared_run (instr : Primitive E F α) (source : FiniteCFG F blocks exits captures) (env : Env α) :
    region instr env (prepared source).erase = region instr env source.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.CapturePassing.prepared_run
    instr source env

theorem Compiled.preserves_run (built : Compiled sig context packets outputs source)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env built.checked.emitted.code.erase :=
  (prepared_run instr source env).symm.trans (built.checked.emitted.preserves_run instr env)

theorem Compiled.seed_value {A : Type 1} {Events : Type → Type}
    (built : Compiled sig context packets outputs source) (instr : Primitive Events F A) (env : Env A) :
    packetValue env built.checked.publicReadback.provenance.seed =
      packValue env (inferSlots source) (packetValue env built.seed) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.CapturePassing.seed_value
    built instr env

/-- Run the actual packed dispatcher with the generated input record.
Only primitive agreement is required at this immutable capture boundary. -/
theorem Compiled.public_run {A : Type 1} (built : Compiled sig context packets outputs source)
    {instr : Primitive (Event sig.Request sig.Reply) F A}
    (env : Env A) (publicAmbient : Env Atom) (atom : A → Atom)
    (prim : PrimitivesAgree instr sig.primitive atom) :
    resultCodec atom <$> (region instr env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      built.checked.publicReadback.packed.observe publicAmbient (built.inputRecord atom env) := by
  rw [← prepared_run instr source env]
  exact built.checked.public_run env publicAmbient _ atom prim (by rw [Compiled.inputRecord, built.seed_value instr env])

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture
