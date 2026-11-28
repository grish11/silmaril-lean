module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardReplay

/-! # Native packed replay across one redundant guard -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open CategoryTheory Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance knownGuardThmsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The pruned program has the same exact input and exit interface. -/
theorem pruned_typed {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (p : RepeatedGuard L n)
    (slots : Fin (n + 1) → Term signature.Instr X Bit) : ValueBranches [X] (p.prunedWith slots) L :=
  KnownGuardReplay.pruned_typed p slots

/-- Reuse the prior pure split instead of testing its slot again. The live
request still runs with the original guard's actual survivor map. -/
theorem repeated_eq_pruned {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : RepeatedGuard L n) (slots : Fin (n + 1) → ReplyFrame.Slot frame) :
    Paper.Extension.Eqv Seed [X] (p.sourceWith (fun j => (slots j).term)).elaborate.val
      (p.prunedWith (fun j => (slots j).term)) L :=
  KnownGuardReplay.repeated_eq_pruned p slots

/-- Pack the pruned program at the original ordered exit interface. -/
@[expose] def RepeatedGuard.packedPruned {L : List (Ty Empty)} {n : Nat} (p : RepeatedGuard L n) :
    Paper.Extension.Singleton.ofType Seed (replyContext (n + 1)) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed (pruned_typed p (readReply (n + 1))).packExits

/-- The original and pruned native programs give equal actual packed arrows. -/
theorem RepeatedGuard.packed_eq_pruned {L : List (Ty Empty)} {n : Nat} (p : RepeatedGuard L n) :
    p.packedSource = p.packedPruned :=
  KnownGuardReplay.packed_eq_pruned p

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
