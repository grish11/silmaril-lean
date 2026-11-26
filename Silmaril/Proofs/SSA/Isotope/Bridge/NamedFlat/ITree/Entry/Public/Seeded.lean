module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public (Seeded packetRecord observeRaw_eq_flat)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA.Semantics (Env)

private theorem valueCodec_id (value : Value Atom) : valueCodec id value = value := by
  induction value <;> simp_all only [valueCodec, id_eq]

theorem observe_eq {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
    {signature : PrimitiveSignature F} {source : CFG V K F} {exits : List K} {fields : K → List V}
    {capture : V} {inputType : PacketType} {outputs : Fin exits.length → PacketType}
    (built : Seeded signature source exits fields capture inputType outputs)
    (initial : V → Value Atom) (packet : Denote inputType) (ambient : Env Atom)
    (checked : built.checkSeed initial packet = true) :
    built.entry.observe ambient (packetRecord packet) =
      Entry.LiveOut.observeRaw signature.primitive exits fields source initial := by
  let namedRecord : Env Atom := fun _ => initial capture
  have prim : PrimitivesAgree signature.primitive signature.primitive id := by
    intro op value
    rw [valueCodec_id, show valueCodec (id : Atom → Atom) = id from funext valueCodec_id, id_map]
  have seed : packetRecord packet built.provenance.slot.val =
      valueCodec id (packetValue namedRecord built.provenance.seed) := by
    rw [valueCodec_id]
    exact (of_decide_eq_true checked).symm
  have aligned := (built.provenance.alignment prim seed).packed
  have result : resultCodec (id : Atom → Atom) = id := by
    funext out
    rcases out with ⟨tag, value⟩
    simp only [resultCodec, valueCodec_id, id_eq]
  rw [result, id_map] at aligned
  let _ := signature.typing
  unfold Program.PackedEntry.observe
  rw [Capture.packed_context_tree signature.primitive built.entry.typed ambient (packetRecord packet), ← aligned,
    observeRaw_eq_flat (fun _ : Fin 1 => capture) built.closed built.accepted initial namedRecord (fun _ => rfl)]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded
