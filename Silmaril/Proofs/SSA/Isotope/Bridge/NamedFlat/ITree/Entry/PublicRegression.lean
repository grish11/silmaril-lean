module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.Defs
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.Isotope (Value)
open Silmaril.SSA.LambdaRTL (CFG upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

private abbrev bit : PacketType := .coprod .unit .unit
private def signature : PrimitiveSignature Unit := ⟨fun _ => bit, fun _ => bit⟩
private abbrev Name := ULift.{1} Nat
private def exits : List Name := [⟨22⟩, ⟨11⟩]
private def fields (_ : Name) : List Name := [⟨7⟩]
private def capture : Name := ⟨14⟩
private def outputs (_ : Fin exits.length) : PacketType := .product .unit (.product bit .unit)

-- The constructor sees only the original RTL and the finite profiles.
-- The second reply either takes a silent backedge or returns to exit one.
private def namedGraph (loops : Bool) : CFG Name Name Unit :=
  ⟨.term (.br ⟨9⟩ (.var capture)),
    [(⟨9⟩, ⟨⟨6⟩, .let1 ⟨7⟩ (.app () (.var ⟨6⟩)) (.term (.br ⟨5⟩ (.var ⟨7⟩)))⟩),
      (⟨5⟩, ⟨⟨7⟩, .term (.case (.val (.var ⟨7⟩)) ⟨19⟩ (.br ⟨22⟩ .unit) ⟨19⟩
        (if loops then .br ⟨5⟩ (.var ⟨7⟩) else .br ⟨11⟩ .unit))⟩)]⟩

private def compiled (loops : Bool) : Option (Constructed signature (namedGraph loops) exits fields capture bit outputs) :=
  construct signature (namedGraph loops) exits fields capture bit (fun _ => bit) outputs

private theorem admitted (loops : Bool) : (compiled loops).isSome := by cases loops <;> decide

private def built (loops : Bool) : Constructed signature (namedGraph loops) exits fields capture bit outputs :=
  (compiled loops).get (admitted loops)

private def packet : Denote bit := .inl ⟨⟩
private def initial (p : Denote bit) : Name → Value Atom :=
  upd (fun _ => .unit) capture (PacketType.encode bit p)

private theorem captureOK (p : Denote bit) : checkCapture capture (initial p) p = true := by
  simp [checkCapture, packetRecord, initial, upd]

example : checkCapture (inputType := bit) capture (initial packet) (.inr ⟨⟩) = false := by decide

private abbrev inclusion (left right : Bool) (packet : Denote bit) :=
  ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
    ∀ x, policy.initial x → ∀ p,
      Silmaril.Elgot.ITree.HandledTrace policy.step x
        (LiveOut.observeRaw signature.primitive exits fields (namedGraph left) (initial packet)) p →
      Silmaril.Elgot.ITree.HandledTrace policy.step x
        (LiveOut.observeRaw signature.primitive exits fields (namedGraph right) (initial packet)) p

private theorem decision (left right : Bool)
    (l : Constructed signature (namedGraph left) exits fields capture bit outputs)
    (r : Constructed signature (namedGraph right) exits fields capture bit outputs) (pkt : Denote bit) :
    l.program.refinementAt? r.program 0 pkt = true ↔ inclusion left right pkt :=
  l.refinementAt?_iff_namedHandledTrace r (initial pkt) pkt (fun _ => .unit) (fun _ => .unit) (captureOK pkt)

set_option maxHeartbeats 1000000 in
private theorem forward : (built true).program.refinement? (built false).program = true := by cbv

example (p : Denote bit) : inclusion true false p :=
  (decision true false (built true) (built false) p).mp (of_decide_eq_true forward 0 p)

set_option maxHeartbeats 1000000 in
example : ¬ inclusion false true packet := by
  intro included
  have accepted := (decision false true (built false) (built true) packet).mpr included
  have rejected : (built false).program.refinementAt? (built true).program 0 packet = false := by cbv
  simp [rejected] at accepted

-- This is a valid structural seed for the phi builder. Its literal erased
-- entry is a constant, so it cannot certify the public slot read in #4232.
private def constantSeed : CFG Name Name Unit :=
  ⟨.term (.br ⟨9⟩ .unit), [(⟨9⟩, ⟨⟨6⟩, .term (.br ⟨22⟩ .unit)⟩)]⟩

private def noFields (_ : Name) : List Name := []
private def unitExits (_ : Fin exits.length) : PacketType := .product .unit .unit
private def constantReadback :=
  NamedFlat.elaborate (Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.attach noFields constantSeed)
    exits (fun _ : Fin 1 => capture)

example :
    (constantReadback.map (fun flat => (Phi.Certified.Entry.OrderedExits.Readback.construct
      signature (fun _ => .unit) unitExits flat).isSome)).getD false = true := by decide

example : (construct signature constantSeed exits noFields capture .unit (fun _ => .unit) unitExits).isNone = true :=
  by decide

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
