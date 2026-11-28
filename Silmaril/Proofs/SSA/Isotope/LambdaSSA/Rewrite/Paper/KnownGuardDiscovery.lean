module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Discovery.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Thms

/-! # Source preservation and exactness of known-guard discovery -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardDiscovery

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.OpenReplay

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

set_option backward.isDefEq.respectTransparency false in
theorem discover_selected {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n)
    {X : Ty Empty} {frame : ReplyFrame X} (slots : Fin n → ReplyFrame.Slot frame) (known : ReplyFrame.Slot frame)
    {terms : Fin n → Term signature.Instr X Bit} {tested : Term signature.Instr X Bit}
    (slotTerms : (fun j => (slots j).term) = terms) (knownTerm : known.term = tested) :
    (KnownGuardContext.discoverWith p slots known slotTerms knownTerm).tree.selectedWith terms =
      p.selectedWith terms := by
  induction p generalizing X with
  | ret | retExpr => rfl
  | request emits label _ _ _ ihl ihr =>
    let next := ReplyFrame.bindSlots slots
    have mapEq := (bindSlots_term slots).trans (congrArg bindReply slotTerms)
    have testEq : known.retainBit.term = retainSlot (A := Bit) tested :=
      congrArg (retainSlot (A := Bit)) knownTerm
    exact congrArg₂ (selectRequest emits label) (ihl next (.retainBit known) mapEq testEq)
      (ihr next (.retainBit known) mapEq testEq)
  | testRequest =>
    simp only [KnownGuardContext.discoverWith]
    split <;> rfl

private theorem slot_term_injective {X : Ty Empty} {frame : ReplyFrame X} :
    Function.Injective (@ReplyFrame.Slot.term X frame) := by
  intro a
  induction a with
  | newest frame =>
    intro b eq
    cases b with
    | newest => rfl
    | retainBit b => cases eq
  | retainUnit a ih =>
    intro b eq
    cases b with
    | retainUnit b =>
      apply congrArg ReplyFrame.Slot.retainUnit
      apply ih
      change Term.seq (.fst _ unit) a.term = Term.seq (.fst _ unit) b.term at eq
      injection eq
  | retainBit a ih =>
    intro b eq
    cases b with
    | newest => cases eq
    | retainBit b =>
      apply congrArg ReplyFrame.Slot.retainBit
      apply ih
      change Term.seq (.fst _ Bit) a.term = Term.seq (.fst _ Bit) b.term at eq
      injection eq

set_option backward.isDefEq.respectTransparency false in
theorem discover_prunesAt_iff {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n)
    {X : Ty Empty} {frame : ReplyFrame X} (slots : Fin n → ReplyFrame.Slot frame) (known : ReplyFrame.Slot frame)
    {terms : Fin n → Term signature.Instr X Bit} {tested : Term signature.Instr X Bit}
    (slotTerms : (fun j => (slots j).term) = terms) (knownTerm : known.term = tested) (route : List Bool) :
    (KnownGuardContext.discoverWith p slots known slotTerms knownTerm).prunesAt route = true ↔
      matchesAt p slots known route := by
  induction p generalizing X route with
  | ret | retExpr =>
    cases route <;> simp [KnownGuardContext.discoverWith, KnownGuardContext.prunesAt, matchesAt]
  | request _ _ _ _ _ ihl ihr =>
    cases route with
    | nil => simp [KnownGuardContext.discoverWith, KnownGuardContext.prunesAt, matchesAt]
    | cons b rest =>
      let next := ReplyFrame.bindSlots slots
      have mapEq := (bindSlots_term slots).trans (congrArg bindReply slotTerms)
      have testEq : known.retainBit.term = retainSlot (A := Bit) tested :=
        congrArg (retainSlot (A := Bit)) knownTerm
      cases b
      · exact ihl next (.retainBit known) mapEq testEq rest
      · exact ihr next (.retainBit known) mapEq testEq rest
  | testRequest =>
    simp only [KnownGuardContext.discoverWith]
    split
    · rename_i h
      cases route with
      | nil => exact iff_of_true rfl (congrArg ReplyFrame.Slot.term h)
      | cons => simp only [KnownGuardContext.prunesAt, matchesAt, Bool.false_eq_true]
    · rename_i h
      cases route with
      | nil => exact iff_of_false (fun eq => Bool.noConfusion eq) (fun eq => h (slot_term_injective eq))
      | cons => simp only [KnownGuardContext.prunesAt, matchesAt, Bool.false_eq_true]

theorem split_source {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    p.discover.source = p.source := by
  let slots := fun j => ReplyFrame.Slot.retainUnit (ReplyFrame.standardSlots n j)
  have mapEq : (fun j => (slots j).term) = fun j => retainSlot (A := unit) (readReply n j) :=
    congrArg (fun read j => retainSlot (A := unit) (read j)) (standardSlots_term n)
  exact congrArg₂ (CaseTree.case unit unit (emitPrefix p.emits (readReply n p.test)))
    (discover_selected p.onFalse slots (slots p.test) mapEq (congrFun mapEq p.test))
    (discover_selected p.onTrue slots (slots p.test) mapEq (congrFun mapEq p.test))

theorem split_prunesAt_iff {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n)
    (onTrue : Bool) (route : List Bool) :
    p.discover.prunesAt onTrue route = true ↔ p.matchesAt onTrue route := by
  let slots := fun j => ReplyFrame.Slot.retainUnit (ReplyFrame.standardSlots n j)
  have mapEq : (fun j => (slots j).term) = fun j => retainSlot (A := unit) (readReply n j) :=
    congrArg (fun read j => retainSlot (A := unit) (read j)) (standardSlots_term n)
  cases onTrue
  · exact discover_prunesAt_iff p.onFalse slots (slots p.test) mapEq (congrFun mapEq p.test) route
  · exact discover_prunesAt_iff p.onTrue slots (slots p.test) mapEq (congrFun mapEq p.test) route

theorem packed_eq_pruned {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    p.packedSource = p.discover.packedPruned := by
  have source := congrArg (fun t : CaseTree signature.Instr (replyContext n) L =>
    Paper.Extension.Singleton.ofRegion Seed t.elaborate.property.packExits) (split_source p)
  exact source.symm.trans p.discover.packed_eq_pruned

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardDiscovery
