module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardTraversal

/-! # Exact guard survival and native soundness of traversal -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance traversalThmsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Survival is membership of the carried projection in the literal guard frame. -/
theorem KnownGuardTraversal.guardSurvives_iff {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin (n + 1) → ReplyFrame.Slot frame) (known : ReplyFrame.Slot frame) (test : Fin (n + 1)) :
    KnownGuardTraversal.guardSurvives slots known test = true ↔
      ∃ j, ReplyFrame.guardSlots slots test j = .retainBit (.retainUnit known) :=
  GuardTraversal.guardSurvives_iff slots known test

/-- Keep the guard's reply subtrees when its literal slot map has no reader
of the transported projection. The projection may still exist in the product. -/
theorem KnownGuardTraversal.guardSurvives_eq_false_iff {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin (n + 1) → ReplyFrame.Slot frame) (known : ReplyFrame.Slot frame) (test : Fin (n + 1)) :
    KnownGuardTraversal.guardSurvives slots known test = false ↔
      ∀ j, ReplyFrame.guardSlots slots test j ≠ .retainBit (.retainUnit known) := by
  rw [← Bool.not_eq_true, KnownGuardTraversal.guardSurvives_iff]
  exact not_exists

/-- Recompiling the kept subtrees preserves the original outward scope. -/
theorem KnownGuardTraversal.render_typed {L : List (Ty Empty)} {tag : Bool} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit} {p : ReadTree L n}
    (c : KnownGuardTraversal L tag slots known p) (rewriteKept : ∀ {n}, ReadTree L n → ReadTree L n)
    (payload : Term signature.Instr X unit) : ValueBranches [X] (c.renderWith rewriteKept payload) L :=
  GuardTraversal.render_typed c rewriteKept payload

/-- The target keeps the original typed exit interface. -/
theorem KnownGuardTraversal.pruned_typed {L : List (Ty Empty)} {tag : Bool} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit} {p : ReadTree L n}
    (c : KnownGuardTraversal L tag slots known p) (payload : Term signature.Instr X unit) :
    ValueBranches [X] (c.pruned payload) L :=
  GuardTraversal.pruned_typed c payload

/-- Replay in a packet that establishes the known tag and its original unit payload. -/
theorem KnownGuardTraversal.eq_pruned_at {Γ L : List (Ty Empty)} {tag : Bool} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit} {p : ReadTree L n}
    (c : KnownGuardTraversal L tag slots known p) (payload : Term signature.Instr X unit)
    {packet u : Tm signature.Instr} (hp : Tm.BranchValue Γ packet X) (hu : Tm.BranchValue Γ u unit)
    (bitFact : ReturnsAt (Γ := Γ) known packet (if tag then .inr u else .inl u))
    (unitFact : ReturnsAt (Γ := Γ) payload packet u) :
    Paper.Extension.Eqv Seed Γ ((p.selectedWith slots).elaborate.val.substVars (Tm.singleSubst packet))
      ((c.pruned payload).substVars (Tm.singleSubst packet)) L :=
  GuardTraversal.eq_pruned_at c payload hp hu bitFact unitFact

/-- Typing for the actual target of the outer split. -/
theorem GuardSplitTraversal.pruned_typed {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {p : SelectedGuardSplit L n} {terms : Fin n → Term signature.Instr X Bit} (t : GuardSplitTraversal p terms) :
    ValueBranches [X] t.pruned L :=
  GuardTraversal.split_typed t

/-- The native rewrite on the exact structural input map. -/
theorem GuardSplitTraversal.eq_pruned {L : List (Ty Empty)} {X : Ty Empty} {n : Nat} {frame : ReplyFrame X}
    (slots : Fin n → ReplyFrame.Slot frame) {terms : Fin n → Term signature.Instr X Bit}
    (mapEq : (fun j => (slots j).term) = terms) {p : SelectedGuardSplit L n} (t : GuardSplitTraversal p terms) :
    Paper.Extension.Eqv Seed [X] (p.sourceWith terms).elaborate.val t.pruned L :=
  GuardTraversal.split_eq_pruned slots mapEq t

@[expose] def GuardSplitTraversal.packedPruned {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {p : SelectedGuardSplit L n} {terms : Fin n → Term signature.Instr X Bit} (t : GuardSplitTraversal p terms) :
    Paper.Extension.Singleton.ofType Seed X ⟶ Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed t.pruned_typed.packExits

/-- Compare the actual packed arrows at the original ordered exits. -/
theorem GuardSplitTraversal.packed_eq_pruned {L : List (Ty Empty)} {X : Ty Empty} {n : Nat} {frame : ReplyFrame X}
    (slots : Fin n → ReplyFrame.Slot frame) {terms : Fin n → Term signature.Instr X Bit}
    (mapEq : (fun j => (slots j).term) = terms) {p : SelectedGuardSplit L n} (t : GuardSplitTraversal p terms) :
    Paper.Extension.Singleton.ofRegion Seed (p.sourceWith terms).elaborate.property.packExits = t.packedPruned :=
  GuardTraversal.split_packed_eq_pruned slots mapEq t

/-- Running discovery on the standard slot map gives native packed equality. -/
theorem SelectedGuardSplit.traverse_packed_eq {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    p.packedSource = p.traverse.packedPruned :=
  p.traverse.packed_eq_pruned (ReplyFrame.standardSlots n) (standardSlots_term n)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
