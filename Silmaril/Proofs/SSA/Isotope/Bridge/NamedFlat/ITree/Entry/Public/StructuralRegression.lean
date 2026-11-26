module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Thms
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Defs
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.RegisterRename.Defs
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Witness.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

private abbrev Name := ULift.{1} Nat
private abbrev bit : PacketType := .coprod .unit .unit
private def signature : PrimitiveSignature Unit := ⟨fun _ => bit, fun _ => bit⟩
private def shared : Name := ⟨4⟩
private def leftRead : Name := ⟨5⟩
private def rightRead : Name := ⟨6⟩
private def liveOut : Name := ⟨9⟩
private def exits : List Name := [⟨22⟩, ⟨11⟩]
private def fields (_ : Name) : List Name := [liveOut]
private def outputs (_ : Fin exits.length) : PacketType := .product .unit (.product bit .unit)

private def graph (first second : Name) : CFG Name Name Unit :=
  ⟨.term (.br ⟨12⟩ (.pair (.var first) (.var second))),
    [(⟨12⟩, ⟨⟨7⟩, .let2 ⟨8⟩ liveOut (.val (.var ⟨7⟩)) (.term (.br ⟨11⟩ .unit))⟩)]⟩

private def build (first second : Name) (firstType : PacketType) :
    Option (StructuralEntry signature (graph first second) exits fields (.product firstType bit) outputs) :=
  constructStructural signature (graph first second) exits fields (.product firstType bit)
    (fun _ => .product firstType bit) outputs

private def left := (build shared leftRead bit).get (by decide)
private def right := (build shared rightRead bit).get (by decide)

private theorem leftFootprint : left.footprint = [(shared, bit), (leftRead, bit)] := by decide
example : right.footprint = [(shared, bit), (rightRead, bit)] := by decide

-- Three independently chosen bits, with one shared register written only
-- when its two occurrences demand the same value.
example : (left.jointStores right).length = 8 := by decide

private def original : Name → Value Atom :=
  upd (upd (upd (fun _ => .unit) shared (.inl .unit)) leftRead (.inr .unit)) rightRead (.inl .unit)

private def leftPacket : Denote (.product bit bit) := (.inl ⟨⟩, .inr ⟨⟩)
private def rightPacket : Denote (.product bit bit) := (.inl ⟨⟩, .inl ⟨⟩)

example : left.entry.observe (fun _ => .unit) (packetRecord (inputType := .product bit bit) leftPacket) =
    LiveOut.observeRaw signature.primitive exits fields (graph shared leftRead) original :=
  left.observe_eq original leftPacket (fun _ => .unit) (by decide)

example : ∃ initial ∈ left.jointStores right,
    ∀ field ∈ left.footprint ++ right.footprint, initial field.1 = original field.1 :=
  left.jointStores_cover right original ⟨leftPacket, by decide⟩ ⟨rightPacket, by decide⟩

private def changedLiveOut : Name → Value Atom := upd original liveOut (.pair .unit .unit)

example : LiveOut.observeRaw signature.primitive exits fields (graph shared leftRead) original =
    LiveOut.observeRaw signature.primitive exits fields (graph shared leftRead) changedLiveOut := by
  apply left.observe_eq_of_capture_agree _ ⟨leftPacket, by decide⟩
  intro field mem
  simp only [leftFootprint, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> decide

-- Repeating a name with disjoint raw encodings empties the domain.
private def conflicting := (build shared shared .unit).get (by decide)
example : (conflicting.jointAssignments right).isEmpty = true := by decide

example : (conflicting.refinementOverCaptures right).emptyDomain = true := by decide
example : (conflicting.refinementOverCaptures right).verdict = some true :=
  conflicting.refinementOverCaptures_vacuous right (by decide)

-- Unequal types with a common encoding still admit exactly the compatible stores.
private def overlapping := (build shared shared (.coprod .unit .empty)).get (by decide)
example : (overlapping.jointStores right).length = 2 := by decide

example : (overlapping.refinementOverCaptures right).emptyDomain = false := by decide
example : overlapping.refinementFromStore? right (fun _ => .unit) = none := by decide

-- Both rows take the same ordered exit. The common value of the repeated
-- capture is the left live-out, while the right live-out uses the other bit.
private def mismatchingStore : Name → Value Atom := upd original rightRead (.inr .unit)
private def overlapPacket : Denote (.product (.coprod .unit .empty) bit) := (.inl ⟨⟩, .inl ⟨⟩)
private def mismatchingPacket : Denote (.product bit bit) := (.inl ⟨⟩, .inr ⟨⟩)

set_option maxHeartbeats 1000000 in
private theorem actualMismatch :
    overlapping.program.refinementBetween? right.program 0 overlapPacket 0 mismatchingPacket = false := by cbv

private theorem storeMismatch :
    overlapping.refinementFromStore? right mismatchingStore = some false := by
  have leftSeed : overlapping.seed? mismatchingStore = some overlapPacket := by decide
  have rightSeed : right.seed? mismatchingStore = some mismatchingPacket := by decide
  change ((overlapping.seed? mismatchingStore).bind fun a => (right.seed? mismatchingStore).bind fun b =>
    some (overlapping.program.refinementBetween? right.program 0 a 0 b)) = some false
  rw [leftSeed, rightSeed]
  exact congrArg some actualMismatch

private theorem overlapFails : (overlapping.refinementOverCaptures right).verdict = some false := by
  have spec := (overlapping.refinementFromStore?_eq_some_iff right mismatchingStore false).mp storeMismatch
  apply (overlapping.refinementOverCaptures_eq_some_iff right false).mpr
  exact ⟨fun impossible => Bool.noConfusion impossible, fun all => spec.2.2.mpr (all mismatchingStore spec.1 spec.2.1)⟩

example : (overlapping.refinementCounterexample? right).isSome = true :=
  (overlapping.refinementCounterexample?_isSome_iff right).mpr overlapFails

private def expectedOverlapWitness : Bool :=
  match overlapping.refinementCounterexample? right with
  | none => false
  | some checked =>
    match checked.val.trace with
    | .result packet =>
      decide (checked.val.initial shared = Value.inl .unit ∧ checked.val.initial rightRead = Value.inr .unit ∧
        packet = (0, Value.inr (.inl (.pair .unit (.pair (.inl .unit) .unit)))))
    | _ => false

#guard expectedOverlapWitness

example : (conflicting.refinementCounterexample? right).isSome = false :=
  Bool.eq_false_iff.mpr fun found => by
    have rejected := (conflicting.refinementCounterexample?_isSome_iff right).mp found
    rw [conflicting.refinementOverCaptures_vacuous right (by decide)] at rejected
    cases rejected

-- This target selects the first unpacked field. The two fields coincide
-- on the one jointly typed capture assignment.
private def matchingGraph : CFG Name Name Unit :=
  {graph shared shared with
    blocks := [(⟨12⟩, ⟨⟨7⟩, .let2 liveOut ⟨8⟩ (.val (.var ⟨7⟩)) (.term (.br ⟨11⟩ .unit))⟩)]}

private def matching : StructuralEntry signature matchingGraph exits fields (.product bit bit) outputs :=
  (constructStructural signature matchingGraph exits fields (.product bit bit) (fun _ => .product bit bit)
    outputs).get (by decide)

private def matchingAssignment : List (Name × Value Atom) := List.replicate 4 (shared, .inl .unit)
private def matchingStore := StructuralSeed.assignmentStore matchingAssignment
private theorem matchingAssignments : overlapping.jointAssignments matching = [matchingAssignment] := by decide

set_option maxHeartbeats 1000000 in
private theorem actualSuccess :
    overlapping.program.refinementBetween? matching.program 0 overlapPacket 0 rightPacket = true := by cbv

private theorem matchingStorePasses : overlapping.refinementFromStore? matching matchingStore = some true := by
  have leftSeed : overlapping.seed? matchingStore = some overlapPacket := by decide
  have rightSeed : matching.seed? matchingStore = some rightPacket := by decide
  change ((overlapping.seed? matchingStore).bind fun a => (matching.seed? matchingStore).bind fun b =>
    some (overlapping.program.refinementBetween? matching.program 0 a 0 b)) = some true
  rw [leftSeed, rightSeed]
  exact congrArg some actualSuccess

private theorem matchingVerdict : (overlapping.refinementOverCaptures matching).verdict = some true := by
  change combineStoreVerdicts ((overlapping.jointStores matching).map
    (overlapping.refinementFromStore? matching)) = some true
  simp only [StructuralEntry.jointStores, matchingAssignments, List.map_cons, List.map_nil]
  change combineStoreVerdicts [overlapping.refinementFromStore? matching matchingStore] = some true
  simp [matchingStorePasses, combineStoreVerdicts]

example : (overlapping.refinementOverCaptures matching).emptyDomain = false := by decide
example : (overlapping.refinementCounterexample? matching).isSome = false :=
  Bool.eq_false_iff.mpr fun found => by
    have rejected := (overlapping.refinementCounterexample?_isSome_iff matching).mp found
    rw [matchingVerdict] at rejected
    cases rejected

#guard !(overlapping.refinementCounterexample? matching).isSome

private def emptyComparison := (conflicting.checkOccurrenceComparison? right).get (by decide)

#guard emptyComparison.overCaptures == ⟨true, some true⟩ && !emptyComparison.counterexample?.isSome

-- An exact dispatcher may type an unused incoming packet differently from
-- the structural seed. Its rows still check, but the pair is unsupported.
private def discardGraph : CFG Name Name Unit :=
  ⟨.term (.br ⟨12⟩ (.var shared)), [(⟨12⟩, ⟨⟨7⟩, .term (.br ⟨11⟩ .unit)⟩)]⟩

private def discard := (constructStructural signature discardGraph exits (fun _ => [])
  bit (fun _ => bit) (fun _ => .product .unit .unit)).get (by decide)

private def unsupported : StructuralEntry signature discardGraph exits (fun _ => [])
    bit (fun _ => .product .unit .unit) :=
  { discard with entry := { discard.entry with
      context := .snoc .nil .unit
      blocks := fun _ => .unit
      typed := by
        let _ := signature.typing
        exact NamedFlat.check_sound _ _ _ _ (by decide) } }

#guard (discard.checkOccurrenceComparison? discard).isSome
#guard (unsupported.checkOccurrenceComparison? discard).isNone
#guard (discard.checkOccurrenceComparison? unsupported).isNone

-- Existing named elaboration can express an injection as an instruction,
-- but the structural public readback takes the operand of a direct jump.
example :
    (constructStructural signature
      {graph shared leftRead with
        entry := .let1 ⟨8⟩ (.inl .unit) (.term (.br ⟨12⟩ (.pair (.var ⟨8⟩) (.var leftRead))))}
      exits fields (.product bit bit) (fun _ => .product bit bit) outputs).isNone = true := by decide

/-! A repeated capture controls the live-out after a completed request. -/

open CategoryTheory
open Silmaril.Elgot.ITree (HasTrace TraceSignature)
open Silmaril.Logic.ITree

private def effectSignature : PrimitiveSignature Unit := ⟨fun _ => .unit, fun _ => bit⟩

private def effectGraph (first second : Name) : CFG Name Name Unit :=
  { graph first second with
    blocks := [(⟨12⟩, ⟨⟨7⟩, .let2 ⟨8⟩ liveOut (.val (.var ⟨7⟩))
      (.let1 ⟨10⟩ (.app () .unit) (.term (.br ⟨11⟩ .unit)))⟩)] }

private abbrev narrowBit : PacketType := .coprod .unit .empty

private abbrev repeatedType (wide : Bool) : PacketType :=
  .coprod .unit (if wide then .product .unit .unit else .empty)

private def repeatedEffect (wide : Bool) : StructuralEntry effectSignature (effectGraph shared shared)
    exits fields (.product (repeatedType wide) bit) outputs :=
  (constructStructural effectSignature (effectGraph shared shared) exits fields
    (.product (repeatedType wide) bit) (fun _ => .product (repeatedType wide) bit) outputs).get
    (by cases wide <;> decide)

private def effectLeft := repeatedEffect false

private def effectRight : StructuralEntry effectSignature (effectGraph shared rightRead) exits fields
    (.product bit bit) outputs :=
  (constructStructural effectSignature (effectGraph shared rightRead) exits fields (.product bit bit)
    (fun _ => .product bit bit) outputs).get (by decide)

private def effectComparison := (effectLeft.checkOccurrenceComparison? effectRight).get (by decide)

set_option maxHeartbeats 1000000 in
private theorem effectRejects : effectLeft.refinementFromStore? effectRight mismatchingStore = some false := by
  have leftSeed : effectLeft.seed? mismatchingStore = some overlapPacket := by decide
  have rightSeed : effectRight.seed? mismatchingStore = some mismatchingPacket := by decide
  change ((effectLeft.seed? mismatchingStore).bind fun a => (effectRight.seed? mismatchingStore).bind fun b =>
    some (effectLeft.program.refinementBetween? effectRight.program 0 a 0 b)) = some false
  rw [leftSeed, rightSeed]
  cbv

private def effectWitness :=
  effectComparison.counterexample?.get (by
    apply effectComparison.counterexample?_isSome_iff.mpr
    have spec := (effectLeft.refinementFromStore?_eq_some_iff effectRight mismatchingStore false).mp effectRejects
    apply (effectLeft.refinementOverCaptures_eq_some_iff effectRight false).mpr
    exact ⟨fun impossible => Bool.noConfusion impossible,
      fun all => spec.2.2.mpr (all mismatchingStore spec.1 spec.2.1)⟩)

-- The extractor keeps the completed opcode exchange and identifies the
-- second ordered exit with the left selected live-out.
#guard match effectWitness.val.trace with
  | .exchange (.ask _) _ (.result packet) =>
    decide (effectWitness.val.initial shared = Value.inl .unit ∧
      effectWitness.val.initial rightRead = Value.inr .unit ∧
      packet = (0, Value.inr (.inl (.pair .unit (.pair (.inl .unit) .unit)))))
  | _ => false

private def enlarged : TraceSignature :=
  ⟨effectSignature.traceSignature.toSignature.sum effectSignature.traceSignature.toSignature⟩

private def relabel : effectSignature.traceSignature ⟶ enlarged :=
  TraceSignature.inr effectSignature.traceSignature.toSignature effectSignature.traceSignature.toSignature

-- The right injection changes the complete event key. The same directed
-- certificate still separates the actual packed starts at the extracted store.
example :
    ∃ (a : Denote (.product narrowBit bit)) (b : Denote (.product bit bit)),
      effectLeft.evalSeed effectWitness.val.initial = PacketType.encode _ a ∧
      effectRight.evalSeed effectWitness.val.initial = PacketType.encode _ b ∧
      HasTrace (effectLeft.entry.observeReindexed relabel (fun _ => .unit) (packetRecord a))
        (relabel.trace effectWitness.val.trace) ∧
      ¬ TraceInstitution.Sat (TraceInstitution.allRepliesModel enlarged)
        (effectLeft.packedRefinementSentenceReindexed effectRight relabel (fun _ => .unit) a b) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := effectLeft.jointStores_typed effectRight effectWitness.property.1
  have distinguished := effectWitness.val.distinguishes_reindexed effectLeft effectRight relabel (fun _ => .unit)
    effectWitness.property a b ha hb
  refine ⟨a, b, ha, hb, distinguished.1, fun accepted => distinguished.2 ?_⟩
  exact accepted () trivial _ ⟨distinguished.1, Silmaril.Elgot.ITree.Replay.allReplies _⟩

-- The checked public starts use different packet types. The original
-- versioned programs read the same store through their version-zero names.
example : effectLeft.observeVersioned mismatchingStore =
    (effectLeft.program.observe 0 overlapPacket >>= fun out => pure (LambdaSSA.FiniteCFG.packedTreeOutput out)) :=
  effectLeft.observeVersioned_eq_public mismatchingStore overlapPacket (by decide)

example : effectRight.observeVersioned mismatchingStore =
    (effectRight.program.observe 0 mismatchingPacket >>= fun out => pure (LambdaSSA.FiniteCFG.packedTreeOutput out)) :=
  effectRight.observeVersioned_eq_public mismatchingStore mismatchingPacket (by decide)

example :
    Silmaril.Elgot.ITree.HandledTrace effectSignature.traceModel.step ()
      (effectLeft.observeVersioned effectWitness.val.initial) effectWitness.val.trace ∧
    ¬ TraceInstitution.Sat effectSignature.traceModel
      (effectLeft.versionedRefinementSentence effectRight effectWitness.val.initial) :=
  let refutes := effectWitness.val.refutes_versioned effectLeft effectRight effectWitness.property
  ⟨refutes.1, refutes.2.2⟩

-- Exact open typing assigns one type per capture slot. The left seed uses
-- the same slot at two distinct, overlapping sum types.
example (captureType : PacketType) :
    letI := effectSignature.typing
    NamedFlat.infer (.snoc .nil captureType)
      (.pair (.bv 0) (.bv 0) : LetCase.LocallyNameless.Tm Empty Unit 1) ≠ some (.product narrowBit bit) := by
  intro same
  change some (Ty.product captureType captureType) = some (.product narrowBit bit) at same
  obtain ⟨first, second⟩ := Ty.product.inj (Option.some.inj same)
  exact (by decide : narrowBit ≠ bit) (first.symm.trans second)

-- The only extra input is the old dispatcher's capture type. Both slots
-- read the same register and the second slot supplies the selected live-out.
private def repeatedAdmission (wide : Bool) : OccurrenceAdmission (repeatedEffect wide) :=
  (repeatedEffect wide).admittedOccurrences (by cases wide <;> decide)

private def leftOccurrences := effectComparison.leftAdmission
private def rightOccurrences := effectComparison.rightAdmission

private def repeatedPacket (wide : Bool) : Denote (.product (repeatedType wide) bit) :=
  (.inl ⟨⟩, .inl ⟨⟩)

example (wide : Bool) :
    (repeatedEffect wide).footprint = [(shared, repeatedType wide), (shared, bit)] ∧
    repeatedType wide ≠ bit := by
  cases wide <;> decide

private noncomputable def repeatedObservation (wide : Bool) :=
  LambdaSSA.Semantics.Interaction.region effectSignature.primitive
    (fun i => (repeatedEffect wide).occurrenceStore (repeatedPacket wide) ⟨i⟩)
      (repeatedAdmission wide).code.erase >>= fun out => pure (LambdaSSA.FiniteCFG.packedTreeOutput out)

private theorem repeatedRun (wide : Bool) :
    LiveOut.observeRaw effectSignature.primitive exits fields (effectGraph shared shared) original =
      repeatedObservation wide :=
  ((repeatedEffect wide).observeRaw_eq_occurrences original (repeatedPacket wide)
    (by cases wide <;> decide)).trans
    ((repeatedAdmission wide).observe_eq_elaborated (repeatedEffect wide) (repeatedPacket wide))

example (leftWide rightWide : Bool) : repeatedObservation leftWide = repeatedObservation rightWide :=
  (repeatedRun leftWide).symm.trans (repeatedRun rightWide)

example : effectLeft.occurrenceContext.toList = [narrowBit, bit] := by decide
example : effectLeft.occurrenceOperand =
    Silmaril.SSA.LambdaRTL.Val.pair (.var ⟨0⟩) (.var ⟨1⟩) := by decide

example : effectLeft.occurrenceStore overlapPacket ⟨0⟩ = mismatchingStore shared ∧
    effectLeft.occurrenceStore overlapPacket ⟨1⟩ = mismatchingStore shared := by decide

-- The wider type would accept the other injection. The repeated capture
-- still supplies a single value and has to pass both occurrence types.
example : (effectLeft.seed? (upd mismatchingStore shared (.inr .unit))).isNone = true := by decide

example : effectLeft.observeVersioned mismatchingStore =
    (LambdaSSA.Semantics.Interaction.region effectSignature.primitive
      (fun i => effectLeft.occurrenceStore overlapPacket ⟨i⟩) leftOccurrences.code.erase >>=
      fun out => pure (LambdaSSA.FiniteCFG.packedTreeOutput out)) :=
  (effectLeft.observeVersioned_eq_occurrences mismatchingStore overlapPacket (by decide)).trans
    (leftOccurrences.observe_eq_elaborated effectLeft overlapPacket)

example : LiveOut.observeRaw effectSignature.primitive exits fields (effectGraph shared rightRead) mismatchingStore =
    (LambdaSSA.Semantics.Interaction.region effectSignature.primitive
      (fun i => effectRight.occurrenceStore mismatchingPacket ⟨i⟩) rightOccurrences.code.erase >>=
      fun out => pure (LambdaSSA.FiniteCFG.packedTreeOutput out)) :=
  (effectRight.observeRaw_eq_occurrences mismatchingStore mismatchingPacket (by decide)).trans
    (rightOccurrences.observe_eq_elaborated effectRight mismatchingPacket)

-- The first compatible capture assignment agrees. Only the second
-- assignment changes the right live-out at the same ordered exit.
example : (effectLeft.jointStores effectRight).map (fun initial => initial rightRead) =
    [.inl .unit, .inr .unit] := by decide

private theorem effectLeftSeed : effectLeft.seed? original = some overlapPacket := by decide
private theorem effectRightSeed : effectRight.seed? original = some rightPacket := by decide

private theorem effectOccurrenceEq :
    effectLeft.observeOccurrences overlapPacket = effectRight.observeOccurrences rightPacket :=
  (effectLeft.observeRaw_eq_occurrences original overlapPacket effectLeftSeed).symm.trans
    ((show LiveOut.observeRaw effectSignature.primitive exits fields (effectGraph shared shared) original =
        LiveOut.observeRaw effectSignature.primitive exits fields (effectGraph shared rightRead) original from rfl).trans
      (effectRight.observeRaw_eq_occurrences original rightPacket effectRightSeed))

private theorem effectAccepts : effectComparison.fromStore? original = some true := by
  apply (effectComparison.fromStore?_eq_some_iff original true).mpr
  refine ⟨overlapPacket, rightPacket, effectLeftSeed, effectRightSeed, ?_⟩
  refine ⟨fun _ policy x hx trace seen => ?_, fun _ => rfl⟩
  change HasTrace (effectRight.observeOccurrences rightPacket) trace
  exact effectOccurrenceEq ▸ seen.1

#guard (effectLeft.jointStores effectRight).map effectComparison.fromStore? ==
  [some true, some false]

-- Reuse a nonempty successful aggregate with the same two occurrence types.
private def matchingComparison := (overlapping.checkOccurrenceComparison? matching).get (by decide)

example (policy : Model.{0, 0} signature.traceSignature.toSignature) :
    TraceInstitution.Sat policy (matchingComparison.sentence overlapPacket rightPacket) :=
  matchingComparison.overCaptures_iff_valid.mp
    matchingVerdict matchingStore overlapPacket rightPacket (by decide) (by decide) policy

-- The original extracted trace still distinguishes the two admitted
-- occurrences at the representative actually returned by the checker.
example :
    ∃ (a : Denote (.product narrowBit bit)) (b : Denote (.product bit bit)),
      effectLeft.seed? effectWitness.val.initial = some a ∧
      effectRight.seed? effectWitness.val.initial = some b ∧
      Silmaril.Elgot.ITree.HandledTrace effectSignature.traceModel.step ()
        (effectLeft.observeOccurrences a) effectWitness.val.trace ∧
      ¬ TraceInstitution.Sat effectSignature.traceModel (effectComparison.sentence a b) := by
  obtain ⟨a, b, ha, hb, seen, _, rejected⟩ :=
    effectComparison.refutes effectWitness.property
  exact ⟨a, b, ha, hb, seen, rejected⟩

example : effectComparison.overCaptures.verdict ≠ some true := by
  intro passed
  obtain ⟨a, b, ha, hb, _, _, rejected⟩ := effectComparison.refutes effectWitness.property
  exact rejected (effectComparison.overCaptures_iff_valid.mp passed
    effectWitness.val.initial a b ha hb effectSignature.traceModel)

example : effectComparison.fromStore? (upd mismatchingStore shared (.inr .unit)) = none := by decide

-- Change both the repeated source capture and the selected final register.
private def registerNames : Name ≃ Name :=
  (Equiv.swap shared ⟨40⟩).trans (Equiv.swap liveOut ⟨90⟩)

private def renamedLeft := effectLeft.rename registerNames.toEmbedding
private def renamedRight := effectRight.rename registerNames.toEmbedding

private def renamedComparison := (renamedLeft.checkOccurrenceComparison? renamedRight).get
  ((effectLeft.checkOccurrenceComparison?_isSome_rename effectRight registerNames.toEmbedding).trans (by decide))

private def renamedLeftOccurrences := renamedComparison.leftAdmission

example : renamedLeft.occurrenceContext.toList = [narrowBit, bit] := by decide
example : renamedLeft.occurrenceGraph = effectLeft.occurrenceGraph :=
  effectLeft.occurrenceGraph_rename registerNames.toEmbedding

example : renamedLeftOccurrences.code.erase = leftOccurrences.code.erase := by
  have same := effectLeft.admitOccurrences_rename registerNames.toEmbedding
  change renamedLeft.admitOccurrences.map (fun admitted => admitted.code.erase) =
    effectLeft.admitOccurrences.map (fun admitted => admitted.code.erase) at same
  rw [← Option.some_get (show renamedLeft.admitOccurrences.isSome from by decide),
    ← Option.some_get (show effectLeft.admitOccurrences.isSome from by decide)] at same
  exact Option.some.inj same

example :
    (renamedLeft.seed? (renameStore registerNames original)).map renamedLeft.observeOccurrences =
      (renamedRight.seed? (renameStore registerNames original)).map renamedRight.observeOccurrences := by
  calc
    _ = (effectLeft.seed? original).map effectLeft.observeOccurrences :=
      effectLeft.decodedOccurrences_rename registerNames original
    _ = (effectRight.seed? original).map effectRight.observeOccurrences := by
      rw [effectLeftSeed, effectRightSeed]
      exact congrArg some effectOccurrenceEq
    _ = _ := (effectRight.decodedOccurrences_rename registerNames original).symm

example :
    ∃ (a : Denote (.product narrowBit bit)) (b : Denote (.product bit bit)),
      renamedLeft.seed? (effectWitness.val.rename registerNames).initial = some a ∧
      renamedRight.seed? (effectWitness.val.rename registerNames).initial = some b ∧
      ¬ TraceInstitution.Sat effectSignature.traceModel (renamedComparison.sentence a b) := by
  have transported := (effectWitness.val.refutes_rename_iff effectLeft effectRight registerNames).mpr effectWitness.property
  obtain ⟨a, b, ha, hb, _, _, rejected⟩ := renamedComparison.refutes transported
  exact ⟨a, b, ha, hb, rejected⟩

example : renamedLeft.footprint = [(⟨40⟩, narrowBit), (⟨40⟩, bit)] := by
  rw [show renamedLeft = effectLeft.rename registerNames.toEmbedding from rfl, effectLeft.footprint_rename]
  decide

example : renamedComparison.fromStore? (renameStore registerNames mismatchingStore) = some false :=
  (effectLeft.refinementFromStore?_rename effectRight registerNames mismatchingStore).trans effectRejects

example : renamedComparison.fromStore? (renameStore registerNames original) = some true :=
  (effectLeft.refinementFromStore?_rename effectRight registerNames original).trans effectAccepts

example : renamedComparison.overCaptures = effectComparison.overCaptures :=
  effectLeft.refinementOverCaptures_rename effectRight registerNames

example : (effectWitness.val.rename registerNames).Refutes renamedLeft renamedRight :=
  (effectWitness.val.refutes_rename_iff effectLeft effectRight registerNames).mpr effectWitness.property

-- Execute the renamed extractor as well as transporting its checked witness.
#guard match renamedComparison.counterexample? with
  | some checked =>
    match checked.val.trace with
    | .exchange (.ask _) _ (.result packet) =>
      decide (checked.val.initial ⟨40⟩ = Value.inl .unit ∧ checked.val.initial shared = Value.unit ∧
        packet = (0, Value.inr (.inl (.pair .unit (.pair (.inl .unit) .unit)))))
    | _ => false
  | none => false

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
