module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.Isotope (Value)
open Silmaril.SSA.LambdaRTL (CFG Val upd)
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

-- The written constant differs from the public slot read. The literal
-- constructor still requires whole-table equality.
private def constantSeed : CFG Name Name Unit :=
  ⟨.term (.br ⟨9⟩ .unit), [(⟨9⟩, ⟨⟨6⟩, .term (.br ⟨22⟩ .unit)⟩)]⟩

private def noFields (_ : Name) : List Name := []
private def unitExits (_ : Fin exits.length) : PacketType := .product .unit .unit

example : (constructSeeded signature constantSeed exits noFields capture .unit (fun _ => .unit) unitExits).isSome :=
  by decide

example : (construct signature constantSeed exits noFields capture .unit (fun _ => .unit) unitExits).isNone = true :=
  by decide

private def pairSeed (first : Val Name) :=
  constructSeeded signature {constantSeed with entry := .term (.br ⟨9⟩ (.pair first .unit))}
    exits noFields capture (.product .unit .unit) (fun _ => .product .unit .unit) unitExits

example : (pairSeed .unit).isSome := by decide
example : (pairSeed (.var capture)).isNone := by decide

private def seededGraph (constant : Bool) : CFG Name Name Unit :=
  if constant then constantSeed else {constantSeed with entry := .term (.br ⟨9⟩ (.var capture))}

private def seedFields (_ : Name) : List Name := [⟨6⟩]
private def seedExits (_ : Fin exits.length) : PacketType := .product .unit (.product .unit .unit)
private def seedBuilt (constant : Bool) :
    Seeded signature (seededGraph constant) exits seedFields capture .unit seedExits :=
  (constructSeeded signature (seededGraph constant) exits seedFields capture .unit (fun _ => .unit) seedExits).get
    (by cases constant <;> decide)

-- The live-out is the register filled by the actual entry jump. Both sides
-- need a seed check, even though their erased internal rows coincide.
example :
    ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
      ∀ x, policy.initial x → ∀ trace,
        Silmaril.Elgot.ITree.HandledTrace policy.step x
          (LiveOut.observeRaw signature.primitive exits seedFields (seededGraph true) (fun _ => .unit)) trace →
        Silmaril.Elgot.ITree.HandledTrace policy.step x
          (LiveOut.observeRaw signature.primitive exits seedFields (seededGraph false) (fun _ => .unit)) trace :=
  ((seedBuilt true).refinementAt?_iff_namedHandledTrace (seedBuilt false)
    (fun _ => .unit) ⟨⟩ (fun _ => .unit) (fun _ => .unit) (by decide) (by decide)).mp (by cbv)

example : (seedBuilt true).checkSeed (fun _ => .pair .unit .unit) ⟨⟩ = true := by decide
example : (seedBuilt false).checkSeed (fun _ => .pair .unit .unit) ⟨⟩ = false := by decide

private def branchCapture (second : Bool) : Name := if second then ⟨15⟩ else capture

-- The two captures are in the same store. Only the register named by the
-- right entry changes. Both targets bind the selected live-out to unit.
private def branchSeedGraph (second : Bool) : CFG Name Name Unit :=
  ⟨.term (.br ⟨9⟩ (.var (branchCapture second))),
    [(⟨9⟩, ⟨⟨7⟩, .term (.case (.val (.var ⟨7⟩))
      ⟨6⟩ (.br ⟨22⟩ .unit) ⟨6⟩ (.br ⟨11⟩ .unit))⟩)]⟩

private def branchBuilt (second : Bool) :
    Seeded signature (branchSeedGraph second) exits seedFields (branchCapture second) bit seedExits :=
  (constructSeeded signature (branchSeedGraph second) exits seedFields (branchCapture second)
    bit (fun _ => bit) seedExits).get (by cases second <;> decide)

private def seedStore : Name → Value Atom :=
  upd (upd (fun _ => .unit) (branchCapture false) (.inl .unit)) (branchCapture true) (.inr .unit)

example : (seedBuilt true).seed? seedStore = some ⟨⟩ := by decide
example : (branchBuilt false).seed? seedStore = some (.inl ⟨⟩) := by decide
example : (branchBuilt true).seed? seedStore = some (.inr ⟨⟩) := by decide
private theorem malformedStore :
    (seedBuilt true).refinementFromStore? (branchBuilt false) (fun _ => .unit) = none := by decide

private abbrev branchInclusion (second : Bool) (initial : Name → Value Atom) :=
  ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
    ∀ x, policy.initial x → ∀ trace,
      Silmaril.Elgot.ITree.HandledTrace policy.step x
        (LiveOut.observeRaw signature.primitive exits seedFields (seededGraph true) initial) trace →
      Silmaril.Elgot.ITree.HandledTrace policy.step x
        (LiveOut.observeRaw signature.primitive exits seedFields (branchSeedGraph second) initial) trace

private theorem branchDecision (second : Bool) (verdict : Bool)
    (computed : (seedBuilt true).refinementFromStore? (branchBuilt second) seedStore = some verdict) :
    verdict = true ↔ branchInclusion second seedStore :=
  (((seedBuilt true).refinementFromStore?_eq_some_iff (branchBuilt second) seedStore verdict).mp computed).2.2

set_option maxHeartbeats 1000000 in
private theorem branchAccepts :
    (seedBuilt true).program.refinementBetween? (branchBuilt false).program 0 ⟨⟩ 0 (.inl ⟨⟩) = true := by cbv

set_option maxHeartbeats 1000000 in
private theorem branchRejects :
    (seedBuilt true).program.refinementBetween? (branchBuilt true).program 0 ⟨⟩ 0 (.inr ⟨⟩) = false := by cbv

private theorem storeVerdict (second : Bool) (initial : Name → Value Atom) (pkt : Denote bit) (verdict : Bool)
    (constant : (seedBuilt true).seed? initial = some ⟨⟩)
    (seed : (branchBuilt second).seed? initial = some pkt)
    (compared : (seedBuilt true).program.refinementBetween? (branchBuilt second).program 0 ⟨⟩ 0 pkt = verdict) :
    (seedBuilt true).refinementFromStore? (branchBuilt second) initial = some verdict := by
  change ((seedBuilt true).seed? initial).bind (fun leftPacket => ((branchBuilt second).seed? initial).bind
    fun rightPacket => some ((seedBuilt true).program.refinementBetween? (branchBuilt second).program
      0 leftPacket 0 rightPacket)) = some verdict
  rw [constant, seed]
  exact congrArg some compared

private theorem firstStorePasses :
    (seedBuilt true).refinementFromStore? (branchBuilt false) seedStore = some true :=
  storeVerdict false seedStore (.inl ⟨⟩) true (by decide) (by decide) branchAccepts

example : branchInclusion false seedStore := (branchDecision false true firstStorePasses).mp rfl

example : ¬ branchInclusion true seedStore :=
  fun included => Bool.noConfusion
    ((branchDecision true false
      (storeVerdict true seedStore (.inr ⟨⟩) false (by decide) (by decide) branchRejects)).mpr included)

-- Keep both RTL tables fixed. The second store varies only the right
-- capture, whose different typed bit leads to the second ordered exit.
private def laterStore : Name → Value Atom := upd seedStore (branchCapture false) (.inr .unit)

private theorem laterStoreFails :
    (seedBuilt true).refinementFromStore? (branchBuilt false) laterStore = some false :=
  storeVerdict false laterStore (.inr ⟨⟩) false (by decide) (by decide) branchRejects

private def finiteStores : Fin 2 → Name → Value Atom :=
  Fin.cases seedStore (fun _ => laterStore)

example : (seedBuilt true).refinementOverStores? (branchBuilt false) (fun _ : Fin 1 => seedStore) = some true := by
  simp only [Seeded.refinementOverStores?, List.ofFn_succ, List.ofFn_zero, firstStorePasses]
  rfl

private theorem finiteFails : (seedBuilt true).refinementOverStores? (branchBuilt false) finiteStores = some false := by
  simp only [Seeded.refinementOverStores?, List.ofFn_succ, List.ofFn_zero, finiteStores,
    Fin.cases_zero, Fin.cases_succ, firstStorePasses, laterStoreFails]
  rfl

example : ¬ ∀ i, branchInclusion false (finiteStores i) :=
  fun valid => Bool.noConfusion
    ((((seedBuilt true).refinementOverStores?_eq_some_iff (branchBuilt false) finiteStores false).mp
      finiteFails).2.mpr valid)

private def mixedStores : Fin 3 → Name → Value Atom :=
  Fin.cases seedStore (Fin.cases laterStore (fun _ _ => .unit))

-- An ill-typed store invalidates the finite interface even after a valid failure.
example : (seedBuilt true).refinementOverStores? (branchBuilt false) mixedStores = none := by
  simp only [Seeded.refinementOverStores?, List.ofFn_succ, List.ofFn_zero, mixedStores,
    Fin.cases_zero, Fin.cases_succ, firstStorePasses, laterStoreFails, malformedStore]
  rfl

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
