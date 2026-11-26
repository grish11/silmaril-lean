module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Thms

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA.Semantics (Env)
open Silmaril.Elgot.ITree (HandledTrace)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source : CFG V K F} {exits : List K} {fields : K → List V}
  {capture : V} {inputType : PacketType} {outputs : Fin exits.length → PacketType}

theorem Constructed.recordAgrees (built : Constructed signature source exits fields capture inputType outputs)
    (packet : Denote inputType) : built.entry.recordAgrees packet (packetRecord packet) := by
  intro i
  simp [built.publicCaptures i, packetRecord, Program.store, upd]

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

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
