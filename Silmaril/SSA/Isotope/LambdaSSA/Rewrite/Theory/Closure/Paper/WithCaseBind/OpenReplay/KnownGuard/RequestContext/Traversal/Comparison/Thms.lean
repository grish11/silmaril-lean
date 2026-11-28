module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedGuardComparison

/-! # Exact readback and checked positive comparison -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic (CaseTree)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (signature)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- The witness is available from an executable positive verdict. -/
theorem EqualityVerdict.sound {claim : Prop} (v : EqualityVerdict claim) (h : v.accepted = true) : claim := by
  cases v with
  | equal proof => exact proof
  | unknown => cases h

local instance comparisonThmsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The actual selected compiler emits syntax with an exact acyclic key. -/
theorem AcyclicSyntax.selected_readable {X : Ty Empty} {L : List (Ty Empty)}
    (p : CaseTree signature.Instr X L) : (AcyclicSyntax.read p.elaborate.val).isSome :=
  SelectedGuardComparison.selected_readable p

/-- Exact target comparison is complete at a scope with an available key. -/
theorem ScopedTarget.compare_accepted_iff {X : Ty Empty} {L : List (Ty Empty)} (left right : ScopedTarget X L)
    (readable : (AcyclicSyntax.read left.val).isSome) :
    (left.compare right).accepted = true ↔ left = right :=
  SelectedGuardComparison.scoped_compare_accepted_iff left right readable

/-- Every target emitted by this traversal has an exact acyclic readback. -/
theorem SelectedAt.normalized_readable {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    (AcyclicSyntax.read p.normalized.val).isSome :=
  SelectedGuardComparison.normalized_readable p

/-- Acceptance is exact for equality of the emitted regions at the shared
typed scope. Packed equality is the positive verdict's proof. -/
theorem SelectedAt.compare_accepted_iff {X : Ty Empty} {L : List (Ty Empty)} (left right : SelectedAt X L) :
    (left.compare right).accepted = true ↔ left.normalized = right.normalized :=
  SelectedGuardComparison.compare_accepted_iff left right

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
