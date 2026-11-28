module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Provenance.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Examples

open Silmaril.Elgot.ITree (Tree HasTrace vis vis_bind diverge diverge_bind)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Logic.ITree.TraceInstitution (Sat)
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph br)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote
  PacketType PrimitiveSignature)
open LambdaSSA (Flat)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues typeModel)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Reverse (Lowered Registers lowerCheckedWith numberedInterface)
open NamedFlat.Entry.Record (Input)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

private abbrev Reg := ULift.{1} Nat
private abbrev SortName := ULift.{1} Unit
private instance : AtomValues SortName := ⟨fun _ => PUnit⟩
private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

private def signature : PrimitiveSignature Unit := ⟨fun _ => .unit, fun _ => .unit⟩
private abbrev Events := Event signature.Request signature.Reply
private def key : signature.Request := ⟨(), ⟨⟩⟩

private instance : HasTy Unit PacketType := signature.typing
private instance : HasTy Unit (Ty SortName) := ⟨fun _ => .unit, fun _ => .unit⟩
private instance : HasEff Unit Bool := ⟨fun _ => true⟩
private abbrev sig : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Unit

attribute [local instance] typeModel

private def model : LambdaSSA.Semantics.Interaction.Typed.Ordered.Model (κ := SortName) Events sig.Instr where
  raw _ v := match v with
    | .unit => vis (Event.ask key) (fun _ => pure .unit)
    | _ => diverge
  instructions := {
    denote := fun _ _ => vis (Event.ask key) (fun _ => pure PUnit.unit)
    denotePure := fun _ h _ => by contradiction
    denote_pure := fun _ h _ => by contradiction }
  compatible _ input := by
    cases input
    change vis (Event.ask key) (fun _ => pure Value.unit) =
      ((vis (Event.ask key) (fun _ => pure PUnit.unit) : Tree Events PUnit.{2}) >>= fun _ => pure Value.unit)
    rw [vis_bind]
    simp only [pure_bind]

private def entryReg : Reg := ⟨0⟩
private def replyReg : Reg := ⟨1⟩
private def carried : Reg := ⟨2⟩
private def header : Reg := ⟨8⟩
private def exits : List (Option Reg) := [some ⟨40⟩, none]

-- The first argument comes from a saved entry capture. The loop passes
-- the actual primitive reply around the backedge φ row.
private def graph (returns : Bool) : Graph Reg Reg Unit :=
  ⟨.term (br header),
    [(header, ⟨[⟨carried, (none, .var entryReg) ::
        (if returns then [] else [(some header, .var replyReg)])⟩],
      .let1 replyReg (.app () (.var carried))
        (.term (if returns then .br none (.pair (.var replyReg) .unit) else br header))⟩)]⟩

private def context : BoundCtx (Ty SortName) 1 := .snoc .nil .unit
private def ports := numberedInterface context exits (fun _ => .unit)
private def captures : Captures Reg context where
  names _ := some entryReg
  distinct i j _ := Subsingleton.elim i j
  privateUnit _ eq := by nomatch eq

private def fields (_ : Option Reg) : List (Reg × Ty SortName) := []
private def admission (returns : Bool) : Admission sig ports fields captures :=
  (admit ports fields captures (graph returns) [entryReg] [(header, [])]
    (fun _ => .product (.product .unit .unit) (.product .unit .unit))).get
      (by cases returns <;> decide)

private def registers : Registers Reg := ⟨⟨1⟩, fun i => ⟨i + 2⟩⟩
private def lowered (returns : Bool) : Lowered ports fields (admission returns).code :=
  (lowerCheckedWith ports fields registers (fun _ => registers.localAt)
    (fun _ => some header) (admission returns).code).get (by cases returns <;> decide)

private def recompiled (returns : Bool) :
    NamedFlat.Entry.LiveOut.Admission sig ports fields (lowered returns).source :=
  (NamedFlat.Entry.LiveOut.admit (P := sig) ports fields (lowered returns).source
    (fun _ => .product (.product (.product .unit .unit) (.product .unit .unit))
      (.product .unit .unit))).get (by cases returns <;> decide)

example : ((lowered false).source.blocks.lookup (some header)).any
    (fun block => block.body.targets.contains (some header)) := by decide

private def packetType : PacketType := .product (.product .unit .unit) (.product .unit .unit)
private def inputs : Fin 1 → PacketType := fun _ => packetType
private def outputs : Fin 2 → PacketType := fun _ => .product .unit .unit
private def localTypes : Fin 1 → PacketType := inputs

-- The public entry receives the literal versioned packet. Its block first
-- opens the saved capture record and the φ argument, then performs the step.
private def program (returns : Bool) : Visible.Program signature inputs outputs where
  locals := 1
  localType := localTypes
  entry _ := .inl 0
  entryType _ := rfl
  block _ :=
    .unpack (.var .here) (.unpack (.var .here) (.unpack (.var (.there (.there (.there .here))))
      (if returns then .apply () (.var (.there .here)) (.inr 1) (.pair (.var .here) .unit)
       else .apply () (.var (.there .here)) (.inl 0)
         (.pair (.pair (.var .here) .unit) (.pair (.var (.there (.there (.there (.there .here))))) .unit)))))

private def names : Fin 1 → Reg := fun _ => entryReg
private def publicContext : BoundCtx PacketType 1 := .snoc .nil packetType

private theorem elaborates (returns : Bool) (input : Fin 1) :
    (NamedFlat.elaborate ((program returns).compile input) (program returns).exits names).isSome := by
  obtain rfl : input = 0 := Subsingleton.elim _ _
  cases returns <;> decide

private def packed (returns : Bool) (input : Fin 1) : Visible.Program.PackedEntry (program returns) input where
  count := 1
  captures := names
  context := publicContext
  blocks := localTypes
  exits := outputs
  target := (NamedFlat.elaborate ((program returns).compile input) (program returns).exits names).get
    (elaborates returns input)
  accepted := (Option.some_get _).symm
  typed := NamedFlat.check_sound _ _ _ _ (by
    obtain rfl : input = 0 := Subsingleton.elim _ _
    cases returns <;> decide)

private def record : Input context := (PUnit.unit, PUnit.unit)
private def ambient : Env Runtime := fun _ => .unit
private def publicAmbient : Env Atom := fun _ => .unit
private def recordAt (_ : Fin 1) : Denote packetType → Env Atom :=
  fun packet _ => Visible.PacketType.encode packetType packet

private theorem agrees (returns : Bool) (input : Fin 1) (packet : Denote packetType) :
    (packed returns input).recordAgrees packet (recordAt input packet) :=
  fun _ => rfl

private def atomCodec (_ : Runtime) : Atom := ⟨⟩

private theorem tableSize (returns : Bool) :
    (CFG.Cyclic.Versioning.compile (CFG.Cyclic.Phi.OrderedExits.lower (admission returns).source)).blocks.length = 1 :=
  by cases returns <;> rfl

private def packetAtEntry : Denote packetType := ((⟨⟩, ⟨⟩), (⟨⟩, ⟨⟩))

private theorem everyPacket (packet : Denote packetType) : packet = packetAtEntry := by
  rcases packet with ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  rfl

private def seed : Val (Fin 1) :=
  .pair (.pair (.var 0) .unit) (.pair (.var 0) .unit)

private def publicBlock (returns : Bool) : Fin ((program returns).compile 0).blocks.length :=
  ⟨0, by change 0 < 1; decide⟩

private def publicSlot (returns : Bool) : Fin (packed returns 0).count :=
  ⟨0, by change 0 < 1; decide⟩

-- Compile the actual public row in the packet-only scope. Its erasure is
-- checked against both the actual φ reverse readback and the public table.
private def packetRow (returns : Bool) : Flat Unit 3 1 :=
  let graph := (program returns).compile 0
  let block := graph.blocks[publicBlock returns].2
  (NamedFlat.body (NamedFlat.labelIndex graph.blocks (program returns).exits)
    (NamedFlat.blockNames block.param) block.body).get (by cases returns <;> decide)

private def provenance (returns : Bool) : Provenance (admission returns).code (packed returns 0).target where
  count := tableSize returns
  exitCount := rfl
  start := ⟨0, by rw [tableSize returns]; decide⟩
  seed := seed
  slot := publicSlot returns
  sourceEntry := by cases returns <;> rfl
  publicEntry :=
    packedEntry_erase_entry (packed returns 0) (publicSlot returns) ⟨0, by change 0 < 3; decide⟩
      (by cases returns <;> rfl) (by cases returns <;> rfl)
  row _ := by
    cases returns
    · exact packetRow false
    · exact packetRow true
  sourceRow i := by
    rcases i with ⟨i, hi⟩
    have bound : i < 1 := Nat.lt_of_lt_of_eq hi (tableSize returns)
    have isZero : i = 0 := by omega
    subst i
    cases returns <;> rfl
  publicRow i := by
    rcases i with ⟨i, hi⟩
    have bound : i < 1 := Nat.lt_of_lt_of_eq hi (tableSize returns)
    have isZero : i = 0 := by omega
    subst i
    cases returns <;> rfl

private theorem primitive_agrees : PrimitivesAgree model.raw signature.primitive atomCodec := by
  intro op value
  cases op
  cases value
  case unit =>
    change valueCodec atomCodec <$> (vis (Event.ask key) fun _ => pure .unit) =
      vis (Event.ask key) (fun _ => pure .unit)
    simp only [map_eq_pure_bind, vis_bind, pure_bind, valueCodec]
  all_goals
    change valueCodec atomCodec <$> (diverge : Tree Events (Value Runtime)) = diverge
    simp only [map_eq_pure_bind, diverge_bind]

private def alignment (returns : Bool) :
    Alignment (admission returns).code (packed returns 0).target model.raw signature.primitive
      (NamedFlat.Entry.inputEnv context record) (recordAt 0 packetAtEntry) atomCodec :=
  (provenance returns).alignment primitive_agrees <|
    (packedEntry_capture_packet (packed returns 0) (publicSlot returns) (by cases returns <;> rfl)
      packetAtEntry _ (agrees returns 0 packetAtEntry)).trans (by cases returns <;> rfl)

private def covered (returns : Bool) (input : Fin 1) (packet : Denote (inputs input)) :
    PublicMatch (admission returns) model record packet (resultCodec atomCodec) (packed returns input)
      publicAmbient (recordAt input packet) ambient := by
  obtain rfl : input = 0 := Subsingleton.elim _ _
  obtain rfl := everyPacket packet
  exact PublicMatch.ofReadback (admission returns) (lowered returns) (recompiled returns)
    model record atomCodec packetAtEntry (packed returns 0) publicAmbient (recordAt 0 packetAtEntry)
    ambient (agrees returns 0 packetAtEntry) (alignment returns)

example :
    resultCodec atomCodec <$> (admission false).observe model record =
      (packed false 0).observe publicAmbient (recordAt 0 packetAtEntry) :=
  (covered false 0 packetAtEntry).source_eq

/-- Coverage follows from the sole entry and the actual inhabitants of
its structural product packet. The public whole-interface test rejects
the change from repeating the request to returning at exit 1. -/
theorem looping_refinement_rejected :
    ¬ ∀ (i : Fin 1) (_ : Denote (inputs i))
        (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature),
      Sat policy ⟨_, resultCodec atomCodec <$> (admission false).observe model record,
        HasTrace (resultCodec atomCodec <$> (admission true).observe model record)⟩ := by
  intro valid
  have verdict := (refinement?_iff_source (P := sig) (left := program false) (right := program true)
    (source := admission false) (target := admission true) (M := model)
    (fun _ _ => record) (resultCodec atomCodec) (covered false) (covered true)).mpr valid
  have rejected : (program false).refinement? (program true) = false := by cbv
  rw [rejected] at verdict
  cases verdict

/-- Exact acceptance of both tables leaves their cross-table relation to
be proved. The same accepted loop readback cannot align to the returning
public table at this packet. -/
theorem returning_table_cannot_align
    (wrong : Alignment (admission false).code (packed true 0).target model.raw signature.primitive
      (NamedFlat.Entry.inputEnv context record) (recordAt 0 packetAtEntry) atomCodec) : False := by
  let matched := PublicMatch.ofReadback (admission false) (lowered false) (recompiled false)
    model record atomCodec packetAtEntry (packed true 0) publicAmbient (recordAt 0 packetAtEntry)
    ambient (agrees true 0 packetAtEntry) wrong
  have accept := (refinementAt?_iff_source (covered false 0 packetAtEntry) matched).mpr
    (fun _ _ _ _ seen => seen.1)
  have reject : (program false).refinementAt? (program true) 0 packetAtEntry = false := by cbv
  rw [reject] at accept
  cases accept

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Examples
