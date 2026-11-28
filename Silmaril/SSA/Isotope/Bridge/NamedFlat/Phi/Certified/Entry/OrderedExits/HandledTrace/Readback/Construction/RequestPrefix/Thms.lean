module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Execution

/-! # Weak execution of typed request-prefix splitting -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Atom Denote PacketType PrimitiveSignature Program Slot)
open Silmaril.Elgot.ITree.Finite (Event)

universe u w

variable {F : Type} {Γ : List PacketType} {blocks exits captures count : Nat}

/-- The allocation leaves old block numbers intact and gives every
continuation a label outside the old range. -/
theorem old_ne_fresh (old : Fin blocks) (fresh : Fin count) :
    oldLabel count old ≠ freshLabel blocks fresh := by
  intro eq
  have val := congrArg Fin.val eq
  change old.val = blocks + fresh.val at val
  exact (Nat.not_le_of_lt old.isLt) (val ▸ Nat.le_add_right blocks fresh.val)

theorem freshLabel_injective : Function.Injective (freshLabel (count := count) blocks) :=
  fun _ _ eq => Fin.ext (Nat.add_left_cancel (congrArg Fin.val eq))

theorem moveExit_old (count : Nat) (i : Fin blocks) :
    moveExit blocks count i.val = i.val := by
  simp [moveExit, i.isLt]

theorem moveExit_external (blocks count : Nat) (i : Fin exits) :
    moveExit blocks count (blocks + i.val) = blocks + count + i.val := by
  simp [moveExit, show ¬ blocks + i.val < blocks by omega]

/-- Unpacking adds slots without modifying the ambient packet or store. -/
theorem Frame.load_ambient {α : Type u} (frame : Frame Γ) (values : Values Γ α) (env : Env α) (i : Nat) :
    frame.load values env (frame.shift + i) = env i :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.load_ambient
    frame values env i

/-- Every logical slot projects its original value at its computed physical
position. This holds uniformly after extending the frame with another reply. -/
theorem Frame.load_slot {α : Type u} (frame : Frame Γ) (values : Values Γ α) (env : Env α) (i : Nat)
    (packet : env i = frame.pack values) {ty : PacketType} (slot : Slot Γ ty) :
    frame.load values env (frame.position i slot) = values slot :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.load_slot
    frame values env i packet slot

variable {sig : PrimitiveSignature F} {outputs : Fin exits → PacketType}
  {packets : Fin blocks → PacketType} {source : FiniteCFG F blocks exits captures}
  {s : Shape sig outputs packets source}

/-- Untouched rows retain their positions and internal targets. Outward
targets move by exactly the number of freshly allocated rows. -/
theorem Shape.table_old (s : Shape sig outputs packets source) (i : Fin blocks) (other : i ≠ s.selected) :
    s.table (oldLabel s.row.requests i) =
      (packets i, (source.block i).erase.renameLabels (moveExit blocks s.row.requests)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.table_old s i other

/-- Every old row keeps its exact packet type, including the split entry
to the request chain. -/
theorem Shape.old_packet (s : Shape sig outputs packets source) (i : Fin blocks) :
    (s.table (oldLabel s.row.requests i)).1 = packets i :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.old_packet s i

/-- An unchanged row has the same weak step. Internal transfers keep
their old indices and packets, and outward transfers keep their relative
exit indices and payloads. -/
theorem Emitted.unchanged_step {E : Type w → Type w} {α : Type u} (emitted : Emitted s)
    (instr : Primitive E F α) (env : Env α) (i : Fin blocks) (other : i ≠ s.selected) (packet : Value α) :
    blockStep instr emitted.code env (oldLabel s.row.requests i, packet) =
      Sum.map id (fun state => (oldLabel s.row.requests state.1, state.2)) <$>
        blockStep instr source env (i, packet) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.unchanged_step
    s emitted instr env i other packet

/-- The same comparison at a typed packet. Transport along the checked old
packet type equality changes neither its codec nor its runtime value. -/
theorem Emitted.unchanged_typed_step {E : Type w → Type w} (emitted : Emitted s)
    (instr : Primitive E F Atom) (env : Env Atom) (i : Fin blocks) (other : i ≠ s.selected)
    (packet : Denote (packets i)) :
    blockStep instr emitted.code env (oldLabel s.row.requests i,
      PacketType.encode _ (cast (congrArg Denote (s.old_packet i).symm) packet)) =
      Sum.map id (fun state => (oldLabel s.row.requests state.1, state.2)) <$>
        blockStep instr source env (i, PacketType.encode _ packet) := by
  have encoded {a b : PacketType} (h : a = b) (p : Denote a) :
      PacketType.encode b (cast (congrArg Denote h) p) = PacketType.encode a p := by cases h; rfl
  rw [encoded (s.old_packet i).symm packet, emitted.unchanged_step instr env i other]

/-- Local simulation on old labels and the selected prefix invariant
preserve the actual complete weak run. Only transfers to fresh continuation
labels stay in the inner iterator. A structural case tree executes after
the final reply and supplies the selected leaf's exact packet. An old
target, including a self-jump, returns control to the outer iterator. -/
theorem Emitted.preserves_run {E : Type w → Type w} {α : Type u} (emitted : Emitted s)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env emitted.code.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.preserves_run
    s emitted instr env

/-- Successful public construction gives exact row provenance for the
split table. Capture and primitive agreement lift the weak-run equation to
the actual typed packed public execution at that record. -/
theorem Emitted.public_run {α : Type 1} (emitted : Emitted s)
    (built : Constructed sig (fun i => (s.table i).1) outputs emitted.code)
    {instr : Primitive (Event sig.Request sig.Reply) F α}
    (env : Env α) (publicAmbient publicRecord : Env Atom) (atom : α → Atom)
    (prim : PrimitivesAgree instr sig.primitive atom)
    (capture : publicRecord built.provenance.slot.val =
      valueCodec atom (packetValue env built.provenance.seed)) :
    resultCodec atom <$> (region instr env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      built.packed.observe publicAmbient publicRecord := by
  let _ := sig.typing
  rw [emitted.preserves_run instr env, Program.PackedEntry.observe, NamedFlat.Capture.packed_context_tree]
  exact (built.provenance.alignment prim capture).packed

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix
