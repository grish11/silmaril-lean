module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Thms
import Silmaril.Semantics.ITree.Reindex.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public (Seeded packetRecord observeRaw_eq_flat)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
open Silmaril.SSA.LambdaRTL (CFG upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA.Semantics (Env)
open Silmaril.Elgot.ITree (HandledTrace TraceLE)

private theorem valueCodec_id (value : Value Atom) : valueCodec id value = value := by
  induction value <;> simp_all only [valueCodec, id_eq]

theorem recordAgrees_of_captures {F : Type} {signature : PrimitiveSignature F} {ty : PacketType}
    {b : Nat} {outputs : Fin b → PacketType} {program : Program signature (fun _ : Fin 1 => ty) outputs}
    (entry : Program.PackedEntry program 0) (captures : ∀ i, entry.captures i = ⟨0⟩)
    (packet : Denote ty) : entry.recordAgrees packet (packetRecord packet) := by
  intro i
  simp [captures i, packetRecord, Program.store, upd]

theorem observe_eq_of_provenance {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
    {signature : PrimitiveSignature F} {source : CFG V K F} {exits : List K} {fields : K → List V}
    {inputType : PacketType} {outputs : Fin exits.length → PacketType}
    {program : Program signature (fun _ : Fin 1 => inputType) outputs} {count : Nat}
    (entry : Program.PackedEntry program 0) (names : Fin count → V)
    (closed : RoundTrip.PacketClosed (LiveOut.attach fields source))
    {flat : LambdaSSA.FiniteCFG F (LiveOut.attach fields source).blocks.length exits.length count}
    (accepted : elaborate (LiveOut.attach fields source) exits names = some flat)
    (provenance : Provenance flat entry.target)
    (initial : V → Value Atom) (packet : Denote inputType) (ambient namedRecord : Env Atom)
    (agrees : ∀ i, namedRecord i.val = initial (names i))
    (checked : packetValue namedRecord provenance.seed = PacketType.encode inputType packet) :
    entry.observe ambient (packetRecord packet) =
      Entry.LiveOut.observeRaw signature.primitive exits fields source initial := by
  have prim : PrimitivesAgree signature.primitive signature.primitive id := by
    intro op value
    rw [valueCodec_id, show valueCodec (id : Atom → Atom) = id from funext valueCodec_id, id_map]
  have seed : packetRecord packet provenance.slot.val =
      valueCodec id (packetValue namedRecord provenance.seed) := by
    rw [valueCodec_id]
    exact checked.symm
  have aligned := (provenance.alignment prim seed).packed
  have result : resultCodec (id : Atom → Atom) = id := by
    funext out
    rcases out with ⟨tag, value⟩
    simp only [resultCodec, valueCodec_id, id_eq]
  rw [result, id_map] at aligned
  let _ := signature.typing
  unfold Program.PackedEntry.observe
  rw [Capture.packed_context_tree signature.primitive entry.typed ambient (packetRecord packet), ← aligned,
    observeRaw_eq_flat names closed accepted initial namedRecord agrees]

theorem observe_eq {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
    {signature : PrimitiveSignature F} {source : CFG V K F} {exits : List K} {fields : K → List V}
    {capture : V} {inputType : PacketType} {outputs : Fin exits.length → PacketType}
    (built : Seeded signature source exits fields capture inputType outputs)
    (initial : V → Value Atom) (packet : Denote inputType) (ambient : Env Atom)
    (checked : built.checkSeed initial packet = true) :
    built.entry.observe ambient (packetRecord packet) =
      Entry.LiveOut.observeRaw signature.primitive exits fields source initial :=
  observe_eq_of_provenance built.entry (fun _ => capture) built.closed built.accepted built.provenance
    initial packet ambient (fun _ => initial capture) (fun _ => rfl) (of_decide_eq_true checked)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {capture rightCapture : V} {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}

theorem seed_eq_some (built : Seeded signature source exits fields capture inputType outputs)
    (initial : V → Value Atom) (packet : Denote inputType) :
    built.seed? initial = some packet ↔ built.checkSeed initial packet = true := by
  let seed := built.evalSeed initial
  change ((PacketType.decode inputType seed).bind fun p =>
    if seed = PacketType.encode inputType p then some p else none) = some packet ↔
    decide (seed = PacketType.encode inputType packet) = true
  rw [decide_eq_true_eq]
  constructor
  · intro found
    obtain ⟨p, _, checked⟩ := Option.bind_eq_some_iff.mp found
    split at checked
    · cases Option.some.inj checked
      assumption
    · contradiction
  · intro checked
    rw [checked, PacketType.decode_encode]
    simp

theorem refinementBetween_namedHandledTrace [DecidableEq F]
    (left : Seeded signature source exits fields capture inputType outputs)
    (right : Seeded signature target exits fields rightCapture rightType outputs)
    (initial : V → Value Atom) (leftPacket : Denote inputType) (rightPacket : Denote rightType)
    (leftAmbient rightAmbient : Env Atom)
    (leftChecked : left.checkSeed initial leftPacket = true) (rightChecked : right.checkSeed initial rightPacket = true) :
    left.program.refinementBetween? right.program 0 leftPacket 0 rightPacket = true ↔
      ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
        ∀ x, policy.initial x → ∀ trace,
          HandledTrace policy.step x (Entry.LiveOut.observeRaw signature.primitive exits fields source initial) trace →
          HandledTrace policy.step x (Entry.LiveOut.observeRaw signature.primitive exits fields target initial) trace := by
  rw [left.program.refinementBetween?_iff_packed right.program leftPacket rightPacket left.entry right.entry
    leftAmbient rightAmbient (packetRecord leftPacket) (packetRecord rightPacket)
    (recordAgrees_of_captures left.entry left.publicCaptures leftPacket)
    (recordAgrees_of_captures right.entry right.publicCaptures rightPacket),
    observe_eq left initial leftPacket leftAmbient leftChecked, observe_eq right initial rightPacket rightAmbient rightChecked]
  refine ⟨fun incl _ _ _ _ seen => incl.handledTrace seen, fun valid trace seen => ?_⟩
  exact (signature.handledTrace_iff _ trace).mp <|
    valid signature.traceModel () trivial trace ((signature.handledTrace_iff _ trace).mpr seen)

theorem refinementFromStore_eq_some [DecidableEq F]
    (left : Seeded signature source exits fields capture inputType outputs)
    (right : Seeded signature target exits fields rightCapture rightType outputs)
    (initial : V → Value Atom) (verdict : Bool) :
    left.refinementFromStore? right initial = some verdict ↔
      (∃ packet, left.checkSeed initial packet = true) ∧ (∃ packet, right.checkSeed initial packet = true) ∧
      (verdict = true ↔
        ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
          ∀ x, policy.initial x → ∀ trace,
            HandledTrace policy.step x (Entry.LiveOut.observeRaw signature.primitive exits fields source initial) trace →
            HandledTrace policy.step x (Entry.LiveOut.observeRaw signature.primitive exits fields target initial) trace) := by
  change ((left.seed? initial).bind fun lp => (right.seed? initial).bind fun rp =>
    some (left.program.refinementBetween? right.program 0 lp 0 rp)) = some verdict ↔ _
  simp only [Option.bind_eq_some_iff, Option.some.injEq, seed_eq_some]
  constructor
  · rintro ⟨leftPacket, hl, rightPacket, hr, rfl⟩
    exact ⟨⟨leftPacket, hl⟩, ⟨rightPacket, hr⟩,
      refinementBetween_namedHandledTrace left right initial leftPacket rightPacket (fun _ => .unit) (fun _ => .unit) hl hr⟩
  · rintro ⟨⟨leftPacket, hl⟩, ⟨rightPacket, hr⟩, valid⟩
    have compare := refinementBetween_namedHandledTrace left right initial leftPacket rightPacket
      (fun _ => .unit) (fun _ => .unit) hl hr
    exact ⟨leftPacket, hl, rightPacket, hr, Bool.eq_iff_iff.mpr (compare.trans valid.symm)⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded
