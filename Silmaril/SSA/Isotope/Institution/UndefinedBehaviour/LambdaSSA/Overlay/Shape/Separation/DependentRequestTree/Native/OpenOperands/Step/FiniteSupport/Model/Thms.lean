module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Classification
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Decision

/-! # The finite-model property of guarded native refinement -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)
open Syntax (Payload StatePrimitives)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {σ : Type v} {n : Nat}
  {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}
  {stores : StateInventory n}

/-- Each deterministic guarded native run has a finite typed derivation or
an infinite path of actual feedback steps. -/
theorem Table.finite_or_infinite (g : Table S R) (a : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (p : Packet R) (s : σ) :
    (∃ rows stop, FiniteRun g a prim p s rows stop) ∨
      Feedback.Infinite (g.feedback a prim) (blockPoint p s) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.finite_or_infinite
    g a prim p s

variable [DecidableEq Φ]

/-- Unsupported readback is independent of the carrier and caller inventory. -/
theorem Table.checkEntries_none_iff :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = none ↔
      g.checkNative raw = false ∨ h.checkNative raw' = false := by
  simp [Table.checkEntries?, Table.compareEntries_none_iff]

theorem Table.checkEntries_accepts_iff :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some true ↔
      g.checkNative raw = true ∧ h.checkNative raw' = true ∧
        ∀ (input : Payload A) (prim : Syntax.Primitives Φ n) (s : Fin n),
          Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
            Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.check_true_iff.trans
    Table.compareEntries_accepts_iff

theorem Table.checkEntries_rejects_iff :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some false ↔
      ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
        some (.counterexample witness) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.check_false_iff

/-- There is no initial state on `Fin 0`, and admission still checks both CFGs. -/
theorem Table.checkEntries_zero (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (stores : StateInventory 0) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some true :=
  Table.checkEntries_accepts_iff.mpr ⟨hg, hh, fun _ _ s => Fin.elim0 s⟩

/-- Exhaustiveness makes a checked empty caller inventory vacuous. -/
theorem Table.checkEntries_empty (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (empty : callers.packets = []) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some true := by
  refine Table.checkEntries_accepts_iff.mpr ⟨hg, hh, fun input _ _ => ?_⟩
  simpa [empty] using callers.complete input


/-- A refuting caller and state give a nonempty rejecting carrier with a
query-count bound from the two actual derivations. -/
theorem Table.rejecting_carrier (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s) :
    ∃ n, 0 < n ∧ RefutationBound g h (decodeLeft input) (decodeRight input) prim s n ∧
      ∀ stores : StateInventory n,
        g.checkAllInterpreters? h raw raw' (decodeLeft input) (decodeRight input) replies left right stores = some false ∧
        g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some false :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.rejecting_carrier
    hg hh callers replies left right input prim s failed

/-- A finite checker rejection is equivalent to a deterministic refutation
on a store type in universe `v`. A finite witness is lifted from `Fin n`. -/
theorem Table.finite_refutation_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    (∃ (n : Nat) (stores : StateInventory n),
      g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some false) ↔
    ∃ (σ : Type v) (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ),
      ¬ Shape.denote (withExitUB raw g.selected)
          (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
        Shape.denote (withExitUB raw' h.selected)
          (Syntax.model prim (h.bindings (decodeRight input))) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.finite_refutation_iff
    hg hh

/-- Acceptance at every finite size includes exact readback and is equivalent
to arbitrary-store deterministic validity. -/
theorem Table.checkEntries_all_accepts_iff :
    (∀ (n : Nat) (stores : StateInventory n),
      g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some true) ↔
      g.checkNative raw = true ∧ h.checkNative raw' = true ∧
        g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.all_accepts_iff

/-- For independently checked endpoints, all finite comparisons suffice
for arbitrary-store refinement. The quantification has no fixed size cutoff. -/
theorem Table.finite_model_property (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight ↔
      ∀ (n : Nat) (stores : StateInventory n),
        g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right stores = some true := by
  simpa only [hg, hh, true_and] using
    (Table.checkEntries_all_accepts_iff (g := g) (h := h) (raw := raw) (raw' := raw')
      (decodeLeft := decodeLeft) (decodeRight := decodeRight)
      (callers := callers) (replies := replies) (left := left) (right := right)).symm

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
