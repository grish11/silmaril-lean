module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Execution

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom PacketType PrimitiveSignature Program)
open NamedFlat.Capture (packEnv)

universe u w
variable {F : Type} {E : Type w → Type w} {α : Type u} {blocks exits captures n : Nat}
  {sig : PrimitiveSignature F} {context : BoundCtx PacketType captures}
  {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
  {source : FiniteCFG F blocks exits captures}

/-- The checked assembly embeds its entire suffix without aliasing. -/
theorem fresh_labels_injective : Function.Injective (freshLabel blocks : Fin n → Fin (blocks + n)) :=
  fun _ _ same => Fin.ext (Nat.add_left_cancel (congrArg Fin.val same))

/-- Splitting an injective allocation into consecutive ranges gives
disjoint labels for the two ranges. -/
theorem left_right_disjoint {l r : Nat} {L : Type} {labels : Fin (l + r) → L}
    (injective : Function.Injective labels) (i : Fin l) (j : Fin r) :
    labels (i.castAdd r) ≠ labels (j.natAdd l) :=
  fun same => (Nat.not_lt_of_ge (Fin.le_coe_natAdd l j)) (injective same ▸ Fin.castAdd_lt r i)

/-- Adding leaves preserves each old block's packet at its original index. -/
theorem EntryTree.old_packet {Γ : List PacketType} (tree : EntryTree sig packets outputs Γ n) (i : Fin blocks) :
    tree.profile (oldLabel n i) = packets i := by
  simp [EntryTree.profile, oldLabel, appendTable_left]

/-- Each request uses the shared prefix step and restores the reply
scope for its checked continuation. Cases preserve the selected payload,
and old iterations and ordered exit payloads are preserved. -/
theorem Outlined.preserves_run (outlined : Outlined sig context packets outputs source)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env outlined.emitted.code.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.preserves_run
    outlined instr env

/-- The assembled table and the structural entry adapter preserve the
original complete weak tree without a termination premise. -/
theorem Compiled.preserves_run (built : Compiled sig context packets outputs source)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env built.prepared.emitted.code.erase :=
  (built.outlined.preserves_run instr env).trans (built.prepared.preserves_run instr env)

theorem Compiled.seed_contract {A : Type 1} {Events : Type → Type}
    (built : Compiled sig context packets outputs source) (instr : Primitive Events F A) (env : Env A) :
    packetValue env built.publicReadback.provenance.seed = packEnv captures env :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.compiled_seed
    built instr env

/-- Exact readback gives the public packed run at the encoded caller
record under primitive agreement. -/
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

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple
