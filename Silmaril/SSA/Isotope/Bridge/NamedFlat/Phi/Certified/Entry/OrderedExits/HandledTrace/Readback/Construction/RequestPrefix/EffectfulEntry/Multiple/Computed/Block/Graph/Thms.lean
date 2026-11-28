module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Thms
public import Silmaril.Semantics.Elgot.Partition.Defs
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Execution

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive region)
open Silmaril.Elgot (iter partitionStepByTarget)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom PacketType PrimitiveSignature Program)

universe u w
variable {F : Type} {E : Type w → Type w} {α : Type u} {blocks exits captures : Nat}
  {sig : PrimitiveSignature F} {context : BoundCtx PacketType captures}
  {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
  {source : FiniteCFG F blocks exits captures} {s : Shape sig packets outputs source}

/-- Every fresh row has exactly one owner and one position in that row's
schedule. This includes empty ranges for unchanged rows. -/
theorem Shape.fresh_injective (s : Shape sig packets outputs source) :
    Function.Injective (fun slot : (i : Fin blocks) × Fin (s.row i).count => s.fresh slot.1 slot.2) :=
  Multiple.fresh_labels_injective.comp finSigmaFinEquiv.injective

theorem Shape.old_cell (s : Shape sig packets outputs source) (i : Fin blocks) :
    s.table (oldLabel s.count i) = (packets i, (s.row i).head (s.fresh i)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.old_cell
    s i

theorem Shape.fresh_cell (s : Shape sig packets outputs source) (i : Fin blocks) (j : Fin (s.row i).count) :
    s.table (s.fresh i j) = (s.row i).cell (s.fresh i) j :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.fresh_cell
    s i j

theorem Compiled.old_row (built : Compiled sig context packets outputs source) (i : Fin blocks) :
    (built.publicReadback.packed.target.block
      ((oldLabel built.shape.count i).cast built.publicReadback.provenance.count)).erase =
      (built.shape.row i).head (built.shape.fresh i) := by
  rw [← built.publicReadback.row_erasure, built.emitted.row_eq, built.shape.old_cell]

theorem Compiled.fresh_row (built : Compiled sig context packets outputs source) (i : Fin blocks)
    (j : Fin (built.shape.row i).count) :
    (built.publicReadback.packed.target.block
      ((built.shape.fresh i j).cast built.publicReadback.provenance.count)).erase =
      ((built.shape.row i).cell (built.shape.fresh i) j).2 := by
  rw [← built.publicReadback.row_erasure, built.emitted.row_eq, built.shape.fresh_cell]

/-- One source step equals the emitted step followed only through fresh
destinations. The packet returned to each old label is unchanged. -/
theorem Emitted.visit (emitted : Emitted s) (instr : Primitive E F α) (env : Env α) (state : BlockInput α blocks) :
    (Sum.map id (fun next => (oldLabel s.count next.1, next.2)) <$> blockStep instr source env state) =
      iter (partitionStepByTarget (blockStep instr emitted.code env)
        (fun next => decide (blocks ≤ next.1.val))) (oldLabel s.count state.1, state.2) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.visit
    s emitted instr env state

/-- All original block visits share a single destination partition.
A transfer to any old label starts a new visit. Complete weak trees agree
without assuming termination or bounding the number of visits. -/
theorem Emitted.preserves_run (emitted : Emitted s) (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env emitted.code.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.preserves_run
    s emitted instr env

/-- Compare the actual packed run using the exact input packet from the
original structural entry and the same visible primitive interpretation. -/
theorem Compiled.public_run {A : Type 1} (built : Compiled sig context packets outputs source)
    {instr : Primitive (Event sig.Request sig.Reply) F A}
    (env : Env A) (publicAmbient publicRecord : Env Atom) (atom : A → Atom)
    (prim : PrimitivesAgree instr sig.primitive atom)
    (capture : publicRecord built.publicReadback.provenance.slot.val =
      valueCodec atom (packetValue env built.publicReadback.provenance.seed)) :
    resultCodec atom <$> (region instr env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      built.publicReadback.packed.observe publicAmbient publicRecord := by
  let _ := sig.typing
  rw [built.emitted.preserves_run instr env, Program.PackedEntry.observe, NamedFlat.Capture.packed_context_tree]
  exact (built.publicReadback.provenance.alignment prim capture).packed

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph
