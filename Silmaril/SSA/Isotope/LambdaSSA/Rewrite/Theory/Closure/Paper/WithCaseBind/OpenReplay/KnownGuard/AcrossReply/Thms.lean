module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.AcrossReply.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardAcrossReply

/-! # A composable native step across a selected request binder -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open CategoryTheory Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance acrossReplyThmsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The ordinary reply binder moves every older logical slot to its successor. -/
theorem GuardAcrossReply.survives_succ {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : GuardAcrossReply L n) (slots : Fin (n + 1) → ReplyFrame.Slot frame)
    (shift : p.afterTest = p.beforeTest.succ) : p.Survives slots :=
  KnownGuardAcrossReply.survives_succ p slots shift

/-- The pruned region has the original typed outward interface. -/
theorem GuardAcrossReply.pruned_typed {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (p : GuardAcrossReply L n)
    (slots : Fin (n + 1) → Term signature.Instr X Bit) : ValueBranches [X] (p.prunedWith slots) L :=
  KnownGuardAcrossReply.pruned_typed p slots

/-- With survival of the typed projection, the native step composes through
the usual case and continuation congruences. The first request's reply remains
an open variable in each of its continuation proofs. -/
theorem GuardAcrossReply.eq_pruned {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : GuardAcrossReply L n) (slots : Fin (n + 1) → ReplyFrame.Slot frame) (survives : p.Survives slots) :
    Paper.Extension.Eqv Seed [X] (p.sourceWith (fun j => (slots j).term)).elaborate.val
      (p.prunedWith (fun j => (slots j).term)) L :=
  KnownGuardAcrossReply.eq_pruned p slots survives

@[expose] def GuardAcrossReply.packedPruned {L : List (Ty Empty)} {n : Nat} (p : GuardAcrossReply L n) :
    Paper.Extension.Singleton.ofType Seed (replyContext (n + 1)) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed (p.pruned_typed (readReply (n + 1))).packExits

/-- Pack the native step at the original ordered exits. -/
theorem GuardAcrossReply.packed_eq_pruned {L : List (Ty Empty)} {n : Nat} (p : GuardAcrossReply L n)
    (survives : p.Survives (ReplyFrame.standardSlots (n + 1))) : p.packedSource = p.packedPruned :=
  KnownGuardAcrossReply.packed_eq_pruned p survives

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
