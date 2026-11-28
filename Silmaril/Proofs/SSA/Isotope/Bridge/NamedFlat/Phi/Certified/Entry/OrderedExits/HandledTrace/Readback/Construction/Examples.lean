module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.Ordered.Defs
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.TwoRequests.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.Construction.Examples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph br)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType Denote PrimitiveSignature Atom)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues typeModel)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Reverse (Lowered Registers lowerCheckedWith numberedInterface)
open NamedFlat.Entry.Record (Input)
open LambdaSSA.Semantics (Env)
open Silmaril.Elgot.ITree (Tree vis vis_bind diverge diverge_bind)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

private abbrev Reg := ULift.{1} Nat
private abbrev SortName := ULift.{1} Unit
private instance : AtomValues SortName := ⟨fun _ => PUnit⟩
private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

private def signature : PrimitiveSignature Unit := ⟨fun _ => .unit, fun _ => .coprod .unit .unit⟩
private instance : HasTy Unit (Ty SortName) := ⟨fun _ => .unit, fun _ => .coprod .unit .unit⟩
private instance : HasEff Unit Bool := ⟨fun _ => true⟩
private abbrev sig : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Unit

private def seedReg : Reg := ⟨0⟩
private def first : Reg := ⟨1⟩
private def reply : Reg := ⟨2⟩
private def choice : Reg := ⟨3⟩
private def left : Reg := ⟨4⟩
private def right : Reg := ⟨5⟩
private def header : Reg := ⟨8⟩
private def dispatch : Reg := ⟨3⟩
private def leftExit : Option Reg := some ⟨90⟩
private def exits : List (Option Reg) := [leftExit, none]

-- Table order differs from numeric label order. The first row receives a
-- unit φ operand, the second a sum supplied by the visible reply.
private def graph : Graph Reg Reg Unit :=
  ⟨.term (br header),
    [(header, ⟨[⟨first, [(none, .var seedReg)]⟩],
      .let1 reply (.app () (.var first)) (.term (br dispatch))⟩),
     (dispatch, ⟨[⟨choice, [(some header, .var reply)]⟩],
      .term (.case (.val (.var choice))
        left (.br leftExit (.pair (.var left) .unit))
        right (.br none (.pair (.pair (.var right) .unit) .unit)))⟩)]⟩

private def context : BoundCtx (Ty SortName) 1 := .snoc .nil .unit
private def ports := numberedInterface context exits (fun i => if i.val = 0 then .unit else .product .unit .unit)
private def captures : Captures Reg context where
  names _ := some seedReg
  distinct i j _ := Subsingleton.elim i j
  privateUnit _ eq := by nomatch eq

private def fields (_ : Option Reg) : List (Reg × Ty SortName) := []
private def packetProfile (ty : Ty SortName) : Ty SortName :=
  .product (.product ty .unit) (.product .unit .unit)

private def admission : Admission sig ports fields captures :=
  (admit ports fields captures graph [seedReg] [(header, []), (dispatch, [])]
    (fun i => packetProfile (if i.val = 0 then .unit else .coprod .unit .unit))).get (by decide)

private def registers : Registers Reg := ⟨⟨1⟩, fun i => ⟨i + 2⟩⟩
private def lowered : Lowered ports fields admission.code :=
  (lowerCheckedWith ports fields registers (fun _ => registers.localAt)
    (fun i => if i.val = 0 then some header else some dispatch) admission.code).get (by decide)

private def built : PublicReadback admission signature :=
  (admission.constructPublic lowered signature).get (by decide)

example : built.compiled.program.locals = 2 := rfl
example : built.packets ⟨0, by decide⟩ =
    .product (.product .unit .unit) (.product .unit .unit) := rfl
example : built.packets ⟨1, by decide⟩ =
    .product (.product (.coprod .unit .unit) .unit) (.product .unit .unit) := rfl
example : built.exits ⟨0, by decide⟩ = .product .unit .unit := rfl
example : built.exits ⟨1, by decide⟩ = .product (.product .unit .unit) .unit := rfl

private def generated := built.compiled.program
private def packet : Denote (built.packets built.compiled.start) := ((⟨⟩, ⟨⟩), (⟨⟩, ⟨⟩))
private def key : signature.Request := ⟨(), ⟨⟩⟩
private abbrev Events := Event signature.Request signature.Reply

private def next (r : signature.Reply key) : generated.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  change (signature.Reply key × PUnit) × (PUnit × PUnit)
  exact ((r, ⟨⟩), (⟨⟩, ⟨⟩))

private def leftReturn : generated.State := by
  refine ⟨⟨.inr ⟨0, by decide⟩, ?_⟩⟩
  change PUnit × PUnit
  exact (⟨⟩, ⟨⟩)

private def rightReturn : generated.State := by
  refine ⟨⟨.inr ⟨1, by decide⟩, ?_⟩⟩
  change (PUnit × PUnit) × PUnit
  exact ((⟨⟩, ⟨⟩), ⟨⟩)

example : generated.step (generated.start 0 packet) = .inl (.request key next) := rfl
example : generated.step (next (.inl ⟨⟩)) = .inr leftReturn := rfl
example : generated.step (next (.inr ⟨⟩)) = .inr rightReturn := rfl

private def rawReply {α : Type 1} : signature.Reply key → Value α
  | .inl _ => .inl .unit
  | .inr _ => .inr .unit

private def typedReply : signature.Reply key → PUnit.{2} ⊕ PUnit.{2}
  | .inl _ => .inl ⟨⟩
  | .inr _ => .inr ⟨⟩

attribute [local instance] typeModel

private def model : LambdaSSA.Semantics.Interaction.Typed.Ordered.Model (κ := SortName) Events sig.Instr where
  raw _ v := match v with
    | .unit => vis (Event.ask key) (fun r => pure (rawReply r))
    | _ => diverge
  instructions := {
    denote := fun _ _ => vis (Event.ask key) (fun r => pure (typedReply r))
    denotePure := fun _ h _ => by contradiction
    denote_pure := fun _ h _ => by contradiction }
  compatible op args := by
    cases op
    cases args
    change vis (Event.ask key) (fun r => pure (rawReply r)) =
      ((vis (Event.ask key) (fun r => pure (typedReply r)) : Tree Events (PUnit.{2} ⊕ PUnit.{2})) >>= _)
    erw [vis_bind]
    congr 1
    funext r
    change pure (rawReply r) =
      ((pure (typedReply r) : Tree Events (PUnit.{2} ⊕ PUnit.{2})) >>= fun result =>
        pure (Silmaril.Isotope.Semantics.encodeValue (AtomValues.carrier (κ := SortName))
          (.coprod .unit .unit) result))
    rw [pure_bind]
    cases r <;> rfl

private def atomCodec (_ : Runtime) : Atom := ⟨⟩

private theorem primitives : PrimitivesAgree model.raw signature.primitive atomCodec := by
  intro op value
  cases op
  cases value
  case unit =>
    change valueCodec atomCodec <$> (vis (Event.ask key) fun r => pure (rawReply r)) =
      vis (Event.ask key) (fun r => pure (Visible.PacketType.encode (signature.reply ()) r))
    simp only [map_eq_pure_bind, vis_bind, pure_bind]
    congr 1
    funext r
    cases r <;> rfl
  all_goals
    change valueCodec atomCodec <$> (diverge : Tree Events (Value Runtime)) = diverge
    simp only [map_eq_pure_bind, diverge_bind]

private def recompiled : NamedFlat.Entry.LiveOut.Admission sig ports fields built.lowered.source :=
  (NamedFlat.Entry.LiveOut.admit (P := sig) ports fields built.lowered.source
    (fun i => .product (packetProfile (if i.val = 0 then .unit else .coprod .unit .unit))
      (.product .unit .unit))).get (by decide)

private def record : Input context := (⟨⟩, ⟨⟩)
private def publicRecord : Env Atom := fun _ => Visible.PacketType.encode _ packet
private def publicAmbient : Env Atom := fun _ => .unit
private def ambient : Env Runtime := fun _ => .unit

private def matched : PublicMatch (input := (0 : Fin 1)) admission model record packet (resultCodec atomCodec) built.compiled.packed
    publicAmbient publicRecord ambient :=
  PublicMatch.ofReadback (input := (0 : Fin 1)) admission built.lowered recompiled model record atomCodec packet built.compiled.packed
    publicAmbient publicRecord ambient (fun _ => rfl) (built.compiled.provenance.alignment primitives rfl)

/-- The independent ordered φ run agrees with the generated, re-read
public packed entry at the supplied structural capture record. -/
theorem generated_observation :
    resultCodec atomCodec <$> admission.observe model record =
      built.compiled.packed.observe publicAmbient publicRecord :=
  matched.source_eq

-- The ordinary flat checker accepts two requests in one row. The public
-- grammar requires a literal jump immediately after its one primitive.
private def twoRequests : LambdaSSA.Flat Unit 2 1 :=
  .let₁ (.op () .unit) (.let₁ (.op () .unit) (.br 1 .unit))

example : NamedFlat.checkBody (fun _ => (.unit : Ty SortName)) context twoRequests = true := rfl

example : Visible.elaborateRow (blocks := 1) (exits := 1) (fun _ => .unit) signature [.unit]
    twoRequests.erase = none := rfl

-- The rejected row itself succeeds when split and compiled through the
-- same public constructor used above.
private def rejected : LambdaSSA.FiniteCFG Unit 1 1 0 :=
  ⟨.br 0 .unit, fun _ => twoRequests⟩

private def splitRejected : TwoRequests.Checked signature .nil .unit (fun _ => .unit) rejected :=
  (TwoRequests.check signature .nil .unit (fun _ => .unit) rejected).get (by decide)

private def compiledRejected :=
  (construct signature (TwoRequests.packets signature .unit splitRejected.shape)
    (fun _ => .unit) splitRejected.emitted.code).get (by decide)

example : compiledRejected.program.locals = 2 := rfl

-- Distinct opcodes let us check the request order, and changing the first
-- reply changes the second request and the payload of the second exit.
private def sumType : PacketType := .coprod .unit .unit

private def orderedSignature : PrimitiveSignature Bool :=
  ⟨fun op => if op then sumType else .unit, fun op => if op then .unit else sumType⟩

private def orderedExits (i : Fin 2) : PacketType :=
  if i.val = 0 then .unit else .product sumType .unit

private def ordered : LambdaSSA.FiniteCFG Bool 1 2 0 :=
  ⟨.br 0 .unit, fun _ => .let₁ (.op false (.bv 0))
    (.let₁ (.op true (.bv 0)) (.br 2 (.pair (.bv 1) (.bv 2))))⟩

private def splitOrdered : TwoRequests.Checked orderedSignature .nil .unit orderedExits ordered :=
  (TwoRequests.check orderedSignature .nil .unit orderedExits ordered).get (by decide)

private def compiledOrdered :=
  (construct orderedSignature (TwoRequests.packets orderedSignature .unit splitOrdered.shape)
    orderedExits splitOrdered.emitted.code).get (by decide)

private def dispatcher := compiledOrdered.program
private def askFirst : orderedSignature.Request := ⟨false, ⟨⟩⟩
private def askSecond (first : orderedSignature.Reply askFirst) : orderedSignature.Request := ⟨true, first⟩

private def resume (first : orderedSignature.Reply askFirst) : dispatcher.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  change PUnit × (PUnit ⊕ PUnit)
  exact (⟨⟩, first)

private def returned (first : orderedSignature.Reply askFirst) : dispatcher.State :=
  ⟨⟨.inr 1, (first, ⟨⟩)⟩⟩

example : dispatcher.step (dispatcher.start 0 ⟨⟩) = .inl (.request askFirst resume) := rfl
example (first : orderedSignature.Reply askFirst) :
    dispatcher.step (resume first) = .inl (.request (askSecond first) (fun _ => returned first)) := rfl

private def noCaptures : Env Atom := fun _ => .unit

private theorem codec_id (x : Value Atom) : valueCodec id x = x := by
  induction x <;> simp_all only [valueCodec, id_eq]

private theorem primitiveIdentity : PrimitivesAgree orderedSignature.primitive orderedSignature.primitive id := by
  intro op value
  rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]

/-- The original second request still receives the first reply, and its
reply remains in the payload at the same ordered exit of the packed dispatcher. -/
theorem ordered_observation :
    (LambdaSSA.Semantics.Interaction.region orderedSignature.primitive noCaptures ordered.erase >>=
      fun out => pure (LambdaSSA.FiniteCFG.packedTreeOutput out)) =
      compiledOrdered.packed.observe noCaptures noCaptures := by
  have codec : resultCodec (id : Atom → Atom) = id := by
    funext out
    cases out
    simp only [resultCodec, codec_id, id_eq]
  simpa only [codec, id_map] using
    splitOrdered.emitted.public_run compiledOrdered noCaptures noCaptures noCaptures id primitiveIdentity rfl

example :
    (LambdaSSA.Semantics.Interaction.region orderedSignature.primitive noCaptures ordered.erase >>=
      fun out => pure (LambdaSSA.FiniteCFG.packedTreeOutput out)) =
      (dispatcher.observe 0 ⟨⟩ >>= fun out => pure (LambdaSSA.FiniteCFG.packedTreeOutput out)) :=
  ordered_observation.trans (compiledOrdered.packed.observe_eq ⟨⟩ _ _ (fun _ => rfl))

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.Construction.Examples
