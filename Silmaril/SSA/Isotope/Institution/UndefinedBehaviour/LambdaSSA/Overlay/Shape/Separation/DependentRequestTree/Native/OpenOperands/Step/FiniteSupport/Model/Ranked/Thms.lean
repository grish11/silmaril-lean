module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Ranked.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Ranked.Bound
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Ranked.Decision

/-! # The ranked guarded checker decides arbitrary-store refinement -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {σ : Type v}

/-- The entry rank bounds successful transfers even when the final
request has no successful reply. The last test needs no transfer. -/
theorem Table.extract_follows_rank (g : Table S R) (ok : g.entryCheck = true) (caller : Payload (R.get g.entry))
    {n : Nat} {probe : Prefix S.replies n}
    (path : (g.extract ok caller).Follows probe) : n ≤ (g.ranks.get g.entry).getD 0 :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked.extract_follows_rank
    g ok caller path

variable [DecidableEq Φ]
  {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

/-- Unknown reports a failed rank check or a failed exact readback. -/
theorem Table.checkRankedEntries_none_iff :
    g.checkRankedEntries? h raw raw' callers decodeLeft decodeRight replies left right = none ↔
      g.checkNative raw = false ∨ h.checkNative raw' = false ∨
        (g.entryCheck = false ∧ h.entryCheck = false) := by
  cases hg : g.entryCheck <;> cases hh : h.entryCheck <;>
    simp [Table.checkRankedEntries?, Table.checkEntries_none_iff, hg, hh]

/-- Any arbitrary-store refutation of a ranked pair gives a rejecting
verdict at the computed finite cutoff. -/
theorem Table.checkRankedEntries_rejects_of_refutation (hg : g.checkNative raw = true)
    (hh : h.checkNative raw' = true) (ranked : g.entryCheck = true ∨ h.entryCheck = true)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s) :
    g.checkRankedEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked.rejects
    hg hh ranked callers replies left right input prim s failed

/-- Both endpoints must pass exact readback. If either entry is ranked,
one comparison decides deterministic refinement across store universes. -/
theorem Table.checkRankedEntries_accepts_iff (hg : g.checkNative raw = true)
    (hh : h.checkNative raw' = true) (ranked : g.entryCheck = true ∨ h.entryCheck = true) :
    g.checkRankedEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked.accepts_iff
    hg hh ranked

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
