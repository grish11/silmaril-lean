module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardRequestContext

/-! # Native alignment of certified request contexts -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- A proof that a slot reads the known projection survives a reply binder. -/
theorem KnownGuardContext.survives_reply {X : Ty Empty} {n : Nat} {slots : Fin n → Term signature.Instr X Bit}
    {known : Term signature.Instr X Bit} {test : Fin n} (survives : slots test = known) :
    bindReply slots test.succ = retainSlot (A := Bit) known :=
  congrArg (retainSlot (A := Bit)) survives

/-- The certified target keeps the outward typing at every leaf and request. -/
theorem KnownGuardContext.pruned_typed {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit}
    (c : KnownGuardContext L slots known) (payload : Term signature.Instr X unit) (b : Bool) :
    ValueBranches [X] (c.pruned payload b) L :=
  KnownGuardRequestContext.context_typed c payload b

/-- Replay the certificate wherever the supplied packet establishes the
transported bit and unit payload. Each request keeps its original reply binder. -/
theorem KnownGuardContext.eq_pruned_at {Γ L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit}
    (c : KnownGuardContext L slots known) (payload : Term signature.Instr X unit) (b : Bool)
    {packet u : Tm signature.Instr} (hp : Tm.BranchValue Γ packet X) (hu : Tm.BranchValue Γ u unit)
    (knownTag : ReturnsAt (Γ := Γ) known packet (if b then .inr u else .inl u))
    (knownUnit : ReturnsAt (Γ := Γ) payload packet u) :
    Paper.Extension.Eqv Seed Γ ((c.tree.selectedWith slots).elaborate.val.substVars (Tm.singleSubst packet))
      ((c.pruned payload b).substVars (Tm.singleSubst packet)) L :=
  KnownGuardRequestContext.context_at c payload b hp hu knownTag knownUnit

theorem KnownGuardSplit.pruned_typed {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} (p : KnownGuardSplit L slots) :
    ValueBranches [X] p.pruned L :=
  KnownGuardRequestContext.split_typed p

/-- The native step holds at the open structural input. Each request reply
remains open in its continuations, and kept leaves retain the original syntax. -/
theorem KnownGuardSplit.eq_pruned {L : List (Ty Empty)} {X : Ty Empty} {n : Nat} {frame : ReplyFrame X}
    (slots : Fin n → ReplyFrame.Slot frame) (p : KnownGuardSplit L (fun j => (slots j).term)) :
    Paper.Extension.Eqv Seed [X] p.source.elaborate.val p.pruned L :=
  KnownGuardRequestContext.eq_pruned slots p

@[expose] def KnownGuardSplit.packedPruned {L : List (Ty Empty)} {n : Nat} (p : KnownGuardSplit L (readReply n)) :
    Paper.Extension.Singleton.ofType Seed (replyContext n) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed p.pruned_typed.packExits

/-- Pack the certified native step at the original ordered typed exits. -/
theorem KnownGuardSplit.packed_eq_pruned {L : List (Ty Empty)} {n : Nat} (p : KnownGuardSplit L (readReply n)) :
    p.packedSource = p.packedPruned :=
  KnownGuardRequestContext.packed_eq_pruned p

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
