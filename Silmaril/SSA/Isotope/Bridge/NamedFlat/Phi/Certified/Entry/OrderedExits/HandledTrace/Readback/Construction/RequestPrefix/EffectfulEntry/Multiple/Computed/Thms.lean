module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Execution

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom PacketType PrimitiveSignature Slot)
open NamedFlat.Capture (packEnv)

universe u w
variable {F : Type} {E : Type w → Type w} {α : Type u} {blocks exits captures : Nat}
  {sig : PrimitiveSignature F} {context : BoundCtx PacketType captures}
  {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
  {source : FiniteCFG F blocks exits captures}

/-- Typed weakening and the raw shift used under the outer reply binder
refer to the same original slot after the schedule. -/
theorem Requests.slots_position {Γ Δ : List PacketType} {ty : PacketType}
    (requests : Requests sig Γ Δ) (slot : Slot Γ ty) :
    position (requests.slots slot) = requests.shift (position slot) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.slots_position
    requests slot

/-- The original operand and its scheduled lets have equal complete
weak trees. Product fields run left to right. A let initializer runs
once, and product destructuring binds the right field at slot zero and
the left field at slot one. -/
theorem Operand.preserves_run {Γ : List PacketType} {ty : PacketType}
    (arg : Operand sig Γ ty) (instr : Primitive E F α) (env : Env α) :
    LambdaSSA.Semantics.Interaction.term instr env arg.written =
      LambdaSSA.Semantics.Interaction.term instr env arg.schedule.term :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.operand_run
    instr env arg

/-- Inserting the scheduled binders preserves the written entry and its actual
old block iteration as complete weak trees. -/
theorem Lifted.preserves_run (lifted : Lifted sig context source) (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env lifted.code.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.preserves_run
    lifted instr env

theorem Compiled.preserves_run (built : Compiled sig context packets outputs source)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env built.checked.prepared.emitted.code.erase :=
  (built.lifted.preserves_run instr env).trans (built.checked.preserves_run instr env)

/-- Compare the original computed request with the exact packed readback
at the encoded caller record and compatible primitive interpretation. -/
theorem Compiled.public_run {A : Type 1} (built : Compiled sig context packets outputs source)
    {instr : Primitive (Event sig.Request sig.Reply) F A}
    (env : Env A) (publicAmbient publicRecord : Env Atom) (atom : A → Atom)
    (prim : PrimitivesAgree instr sig.primitive atom)
    (capture : publicRecord built.checked.publicReadback.provenance.slot.val = valueCodec atom (packEnv captures env)) :
    resultCodec atom <$> (region instr env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      built.checked.publicReadback.packed.observe publicAmbient publicRecord := by
  rw [built.lifted.preserves_run instr env]
  exact built.checked.public_run env publicAmbient publicRecord atom prim capture

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed
