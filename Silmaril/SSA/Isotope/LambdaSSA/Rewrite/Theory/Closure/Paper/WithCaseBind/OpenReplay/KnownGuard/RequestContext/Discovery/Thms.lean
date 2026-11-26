module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Discovery.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardDiscovery

/-! # Exactness and native soundness of selected guard discovery -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance discoveryThmsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Discovery leaves the selected source tree exactly as the compiler receives it. -/
theorem KnownGuardContext.discover_selected {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n)
    {X : Ty Empty} {frame : ReplyFrame X} (slots : Fin n → ReplyFrame.Slot frame) (known : ReplyFrame.Slot frame)
    {terms : Fin n → Term signature.Instr X Bit} {tested : Term signature.Instr X Bit}
    (slotTerms : (fun j => (slots j).term) = terms) (knownTerm : known.term = tested) :
    (KnownGuardContext.discoverWith p slots known slotTerms knownTerm).tree.selectedWith terms =
      p.selectedWith terms :=
  KnownGuardDiscovery.discover_selected p slots known slotTerms knownTerm

/-- Discovery prunes exactly the reachable guards whose typed test is the transported projection. -/
theorem KnownGuardContext.discover_prunesAt_iff {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n)
    {X : Ty Empty} {frame : ReplyFrame X} (slots : Fin n → ReplyFrame.Slot frame) (known : ReplyFrame.Slot frame)
    {terms : Fin n → Term signature.Instr X Bit} {tested : Term signature.Instr X Bit}
    (slotTerms : (fun j => (slots j).term) = terms) (knownTerm : known.term = tested) (route : List Bool) :
    (KnownGuardContext.discoverWith p slots known slotTerms knownTerm).prunesAt route = true ↔
      matchesAt p slots known route :=
  KnownGuardDiscovery.discover_prunesAt_iff p slots known slotTerms knownTerm route

/-- The certificate compiles to the actual selected source of the original split. -/
theorem SelectedGuardSplit.discover_source {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    p.discover.source = p.source :=
  KnownGuardDiscovery.split_source p

/-- Completeness for exact typed projection matches along ordinary request paths. -/
theorem SelectedGuardSplit.discover_prunesAt_iff {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n)
    (onTrue : Bool) (route : List Bool) :
    p.discover.prunesAt onTrue route = true ↔ p.matchesAt onTrue route :=
  KnownGuardDiscovery.split_prunesAt_iff p onTrue route

/-- A native packed equality at the original input and ordered typed exits. -/
theorem SelectedGuardSplit.packed_eq_pruned {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    p.packedSource = p.discover.packedPruned :=
  KnownGuardDiscovery.packed_eq_pruned p

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
