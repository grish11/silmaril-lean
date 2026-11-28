module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Native.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Native

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Native

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom PacketType PrimitiveSignature)
open Silmaril.Elgot.ITree.Finite (Event)

universe u w
variable {F : Type} {Events : Type w → Type w} {A : Type u} {blocks exits captures : Nat}
  {sig : PrimitiveSignature F} {context : BoundCtx PacketType captures}
  {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
  {source : FiniteCFG F blocks exits captures}

theorem Compiled.preserves_run (built : Compiled sig context packets outputs source)
    (instr : Primitive Events F A) (env : Env A) :
    region instr env source.erase = region instr env built.code.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Native.preserves_run
    built instr env

/-- With the same primitive trees, the actual packed run from the original
capture record agrees at every reply and retains the original exit tags. -/
theorem Compiled.packed_run (built : Compiled sig context packets outputs source)
    (instr : Primitive Events F A) (env ambient : Env A) :
    built.observe instr ambient (NamedFlat.Capture.packEnv captures env) =
      (region instr env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) := by
  let _ := sig.typing
  rw [Compiled.observe, Compiled.packedRegion, NamedFlat.Capture.packed_context_tree, ← built.preserves_run]

/-- The encoded capture record and compatible primitive interpretation
give the same complete weak tree as the original written graph. -/
theorem Compiled.packed_run_of_agree {A : Type 1} (built : Compiled sig context packets outputs source)
    {instr : Primitive (Event sig.Request sig.Reply) F A}
    (env : Env A) (ambient : Env Atom) (atom : A → Atom)
    (prim : PrimitivesAgree instr sig.primitive atom) :
    resultCodec atom <$> (region instr env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      built.observe sig.primitive ambient (NamedFlat.Capture.packEnv captures (valueCodec atom ∘ env)) := by
  rw [built.packed_run]
  exact (prim.sameGraph source env).packed

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Native
