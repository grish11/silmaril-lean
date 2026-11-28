module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Normalize
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Readback
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction hiding Row Table
open OpenOperands (CallerEnumeration ReplyEnumeration ConfigurationEnumeration)
open OpenOperands.Silent
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload Primitives model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {A : Syntax.Ty}
  {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

theorem accepts_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight := by
  have guard : (g.checkNative raw && h.checkNative raw') = true := Bool.and_eq_true_iff.mpr ⟨hg, hh⟩
  rw [OpenOperands.Silent.Table.checkEntries?, ite_eq_left guard,
    OpenOperands.Table.checkReachableEntries_accepts_iff (guarded_readback_self _) (guarded_readback_self _)]
  unfold OpenOperands.Silent.Table.DeterministicRefines OpenOperands.Table.DeterministicRefines
  constructor
  · intro normalized σ input prim s
    rw [normalize_observes g raw hg (decodeLeft input) prim s,
      normalize_observes h raw' hh (decodeRight input) prim s]
    exact normalized σ input prim s
  · intro original σ input prim s
    have passed := original σ input prim s
    rw [normalize_observes g raw hg (decodeLeft input) prim s,
      normalize_observes h raw' hh (decodeRight input) prim s] at passed
    exact passed

theorem accepts_cutoff_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    let n := g.cutoff h callers decodeLeft decodeRight replies left right
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      ∀ (input : Payload A) (prim : Primitives Φ n) (s : Fin n),
        Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings (decodeLeft input))) s ≤
          Shape.denote (withExitUB raw' h.selected) (model prim (h.visible.bindings (decodeRight input))) s := by
  dsimp only [OpenOperands.Silent.Table.cutoff]
  have guard : (g.checkNative raw && h.checkNative raw') = true := Bool.and_eq_true_iff.mpr ⟨hg, hh⟩
  rw [OpenOperands.Silent.Table.checkEntries?, ite_eq_left guard, OpenOperands.Table.checkReachableEntries?,
    OpenOperands.Table.checkEntries_accepts_iff]
  simp only [guarded_readback_self, true_and]
  constructor
  · intro normalized input prim s
    rw [normalize_observes g raw hg (decodeLeft input) prim s,
      normalize_observes h raw' hh (decodeRight input) prim s]
    exact normalized input prim s
  · intro original input prim s
    have passed := original input prim s
    rw [normalize_observes g raw hg (decodeLeft input) prim s,
      normalize_observes h raw' hh (decodeRight input) prim s] at passed
    exact passed

theorem none_iff :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = none ↔
      g.checkNative raw = false ∨ h.checkNative raw' = false := by
  cases gl : g.checkNative raw <;> cases hr : h.checkNative raw' <;>
    simp [OpenOperands.Silent.Table.checkEntries?, gl, hr,
      OpenOperands.Table.checkReachableEntries_none_iff, guarded_readback_self]

theorem rejects_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false ↔
      ¬ g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight := by
  rw [← accepts_iff hg hh]
  cases found : g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right with
  | none =>
    have unsupported := none_iff.mp found
    simp [hg, hh] at unsupported
  | some b => cases b <;> simp


end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent
