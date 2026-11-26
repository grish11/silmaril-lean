module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Seeded

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open Silmaril.Elgot.ITree (HandledTrace)
open Phi.Certified.Entry.OrderedExits.Readback (Provenance packetValue)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source : CFG V K F} {exits : List K} {fields : K → List V}
  {capture : V} {inputType : PacketType} {outputs : Fin exits.length → PacketType}

theorem Constructed.recordAgrees (built : Constructed signature source exits fields capture inputType outputs)
    (packet : Denote inputType) : built.entry.recordAgrees packet (packetRecord packet) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded.recordAgrees_of_captures
    built.entry built.publicCaptures packet

theorem Constructed.captureAgrees (built : Constructed signature source exits fields capture inputType outputs)
    (initial : V → Value Atom) (packet : Denote inputType)
    (checked : checkCapture capture initial packet = true) :
    ∀ i, packetRecord packet i.val = initial (built.readback.captures i) := by
  intro i
  rw [built.namedCaptures i]
  exact (of_decide_eq_true checked).symm

/-- Successful construction and a matching capture identify the packed and
original-runner observations. -/
theorem Constructed.observe_eq (built : Constructed signature source exits fields capture inputType outputs)
    (initial : V → Value Atom) (packet : Denote inputType) (ambient : Env Atom)
    (checked : checkCapture capture initial packet = true) :
    built.entry.observe ambient (packetRecord packet) =
      LiveOut.observeRaw signature.primitive exits fields source initial :=
  built.readback.observe_eq initial ambient _ (built.captureAgrees initial packet checked)

/-- The existing packed verdict compares the original RTL runners once the
common initial store supplies the public packet at the captured register. -/
theorem Constructed.refinementAt?_iff_namedHandledTrace [DecidableEq F] {target : CFG V K F}
    (left : Constructed signature source exits fields capture inputType outputs)
    (right : Constructed signature target exits fields capture inputType outputs)
    (initial : V → Value Atom) (packet : Denote inputType) (leftAmbient rightAmbient : Env Atom)
    (checked : checkCapture capture initial packet = true) :
    left.program.refinementAt? right.program 0 packet = true ↔
      ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
        ∀ x, policy.initial x → ∀ trace,
          HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields source initial) trace →
          HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields target initial) trace :=
  Public.refinementAt?_iff_namedHandledTrace packet left.entry right.entry left.readback right.readback
    initial leftAmbient rightAmbient (packetRecord packet) (packetRecord packet)
    (left.captureAgrees initial packet checked) (right.captureAgrees initial packet checked)
    (left.recordAgrees packet) (right.recordAgrees packet)

theorem Seeded.recordAgrees (built : Seeded signature source exits fields capture inputType outputs)
    (packet : Denote inputType) : built.entry.recordAgrees packet (packetRecord packet) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded.recordAgrees_of_captures
    built.entry built.publicCaptures packet

/-- A checked structural seed aligns the named jump with the actual
public entry. Internal rows agree exactly and the result retains ordered
exits and the original runner's selected live-outs. -/
theorem Seeded.observe_eq (built : Seeded signature source exits fields capture inputType outputs)
    (initial : V → Value Atom) (packet : Denote inputType) (ambient : Env Atom)
    (checked : built.checkSeed initial packet = true) :
    built.entry.observe ambient (packetRecord packet) =
      LiveOut.observeRaw signature.primitive exits fields source initial :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded.observe_eq built initial packet ambient checked

/-- Exact internal rows and a matching pure entry seed suffice for the
original-runner equation at any finite source capture layout. -/
theorem observe_eq_of_provenance {count : Nat}
    {program : Program signature (fun _ : Fin 1 => inputType) outputs}
    (entry : Program.PackedEntry program 0) (names : Fin count → V)
    (closed : RoundTrip.PacketClosed (Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.attach fields source))
    {flat : FiniteCFG F (Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.attach fields source).blocks.length exits.length count}
    (accepted : NamedFlat.elaborate (Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.attach fields source) exits names = some flat)
    (provenance : Provenance flat entry.target)
    (initial : V → Value Atom) (packet : Denote inputType) (ambient namedRecord : Env Atom)
    (agrees : ∀ i, namedRecord i.val = initial (names i))
    (checked : packetValue namedRecord provenance.seed = PacketType.encode inputType packet) :
    entry.observe ambient (packetRecord packet) =
      LiveOut.observeRaw signature.primitive exits fields source initial :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded.observe_eq_of_provenance entry names closed accepted
    provenance initial packet ambient namedRecord agrees checked

/-- Decoding succeeds at exactly the packets that pass the seed check. -/
theorem Seeded.seed?_eq_some_iff (built : Seeded signature source exits fields capture inputType outputs)
    (initial : V → Value Atom) (packet : Denote inputType) :
    built.seed? initial = some packet ↔ built.checkSeed initial packet = true :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded.seed_eq_some built initial packet

/-- Compare the two checked entry packets at one common initial named
store. Each packed entry uses its own type and capture record. -/
theorem Seeded.refinementBetween?_iff_namedHandledTrace [DecidableEq F]
    {target : CFG V K F} {rightCapture : V} {rightType : PacketType}
    (left : Seeded signature source exits fields capture inputType outputs)
    (right : Seeded signature target exits fields rightCapture rightType outputs)
    (initial : V → Value Atom) (leftPacket : Denote inputType) (rightPacket : Denote rightType)
    (leftAmbient rightAmbient : Env Atom)
    (leftChecked : left.checkSeed initial leftPacket = true) (rightChecked : right.checkSeed initial rightPacket = true) :
    left.program.refinementBetween? right.program 0 leftPacket 0 rightPacket = true ↔
      ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
        ∀ x, policy.initial x → ∀ trace,
          HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields source initial) trace →
          HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields target initial) trace :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded.refinementBetween_namedHandledTrace left right initial
    leftPacket rightPacket leftAmbient rightAmbient leftChecked rightChecked

/-- The shared-packet verdict is the diagonal case of the two starts. -/
theorem Seeded.refinementAt?_iff_namedHandledTrace [DecidableEq F] {target : CFG V K F} {rightCapture : V}
    (left : Seeded signature source exits fields capture inputType outputs)
    (right : Seeded signature target exits fields rightCapture inputType outputs)
    (initial : V → Value Atom) (packet : Denote inputType) (leftAmbient rightAmbient : Env Atom)
    (leftChecked : left.checkSeed initial packet = true) (rightChecked : right.checkSeed initial packet = true) :
    left.program.refinementAt? right.program 0 packet = true ↔
      ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
        ∀ x, policy.initial x → ∀ trace,
          HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields source initial) trace →
          HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields target initial) trace :=
  left.refinementBetween?_iff_namedHandledTrace right initial packet packet
    leftAmbient rightAmbient leftChecked rightChecked

/-- A store verdict exists exactly when both entries have typed seeds.
Its Boolean decides directed handled-trace inclusion on the original
runners for this store, with the shared primitive and exit observations. -/
theorem Seeded.refinementFromStore?_eq_some_iff [DecidableEq F]
    {target : CFG V K F} {rightCapture : V} {rightType : PacketType}
    (left : Seeded signature source exits fields capture inputType outputs)
    (right : Seeded signature target exits fields rightCapture rightType outputs)
    (initial : V → Value Atom) (verdict : Bool) :
    left.refinementFromStore? right initial = some verdict ↔
      (∃ packet, left.checkSeed initial packet = true) ∧ (∃ packet, right.checkSeed initial packet = true) ∧
      (verdict = true ↔
        ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
          ∀ x, policy.initial x → ∀ trace,
            HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields source initial) trace →
            HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields target initial) trace) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Seeded.refinementFromStore_eq_some left right initial verdict

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
