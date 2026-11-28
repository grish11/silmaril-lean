module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.BranchEntry.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Execution

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom PacketType PrimitiveSignature Program)
open NamedFlat.Capture (packEnv)

universe u w
variable {F : Type} {E : Type w → Type w} {α : Type u} {blocks exits captures : Nat}
  {sig : PrimitiveSignature F} {context : BoundCtx PacketType captures}
  {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
  {source : FiniteCFG F blocks exits captures}

/-- The selected leaf runs in the existing prefix frame. Returning to an
old block resumes the original outer iteration, including backedges. -/
theorem Outlined.preserves_run (outlined : Outlined sig context packets outputs source)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env outlined.code.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.preserves_run
    outlined instr env

/-- Outlining the request and materializing the entry preserve the
complete weak tree, with no termination premise. -/
theorem Compiled.preserves_run (built : Compiled sig context packets outputs source)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env built.prepared.emitted.code.erase :=
  (built.outlined.preserves_run instr env).trans (built.prepared.preserves_run instr env)

/-- The public seed is the canonical capture record at the written entry. -/
theorem Compiled.seed_contract {A : Type 1} {Events : Type → Type}
    (built : Compiled sig context packets outputs source) (instr : Primitive Events F A) (env : Env A) :
    packetValue env built.publicReadback.provenance.seed = packEnv captures env :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.compiled_seed
    built instr env

/-- Compare the original written CFG with the exact public packed readback
at the encoded caller record, using compatible primitive interpretations. -/
theorem Compiled.public_run {A : Type 1} (built : Compiled sig context packets outputs source)
    {instr : Primitive (Event sig.Request sig.Reply) F A}
    (env : Env A) (publicAmbient publicRecord : Env Atom) (atom : A → Atom)
    (prim : PrimitivesAgree instr sig.primitive atom)
    (capture : publicRecord built.publicReadback.provenance.slot.val = valueCodec atom (packEnv captures env)) :
    resultCodec atom <$> (region instr env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      built.publicReadback.packed.observe publicAmbient publicRecord := by
  let _ := sig.typing
  rw [built.preserves_run instr env, Program.PackedEntry.observe, NamedFlat.Capture.packed_context_tree]
  exact (built.publicReadback.provenance.alignment prim
    (by simpa only [built.seed_contract instr env] using capture)).packed

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry
