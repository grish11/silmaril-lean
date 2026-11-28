module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Decision

/-! # Exact reachable cutoffs at original packed dispatcher endpoints -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Category.FiniteIteration hiding Table
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives Primitives model)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {A : Syntax.Ty}
  {g : Table S R} {h : Table S T} {a : Payload (R.get g.entry)} {b : Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

/-- The recorded prefix reaches the mismatching pair through exactly
typed shared request replies. -/
theorem Table.productMismatch_path {point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (found : g.productMismatch? h a b replies left right = some (point, trail)) :
    ProductPath (g.productEdges h a b replies left right) (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail point ∧
      (g.head left a point.1).checkPair replies (fun _ _ => true) (h.head right b point.2) = false :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.mismatch_path
    found

variable {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A} {decodeLeft : Payload A → Payload (R.get g.entry)}
  {decodeRight : Payload A → Payload (T.get h.entry)}

/-- The unknown verdict is exactly failure of one of the original readbacks. -/
theorem Table.checkEntries_none_iff :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = none ↔
      g.checkNative raw = false ∨ h.checkNative raw' = false :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.none_iff

/-- Rejection supplies a typed caller and a total deterministic
interpreter on the computed finite carrier, refuting the original CFGs. -/
theorem Table.checkEntries_witness
    (rejected : g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false) :
    let n := g.cutoff h callers decodeLeft decodeRight replies left right
    ∃ (input : Payload A) (prim : Primitives Φ n) (s : Fin n),
      ¬ Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings (decodeLeft input))) s ≤
        Shape.denote (withExitUB raw' h.selected) (model prim (h.visible.bindings (decodeRight input))) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.witness
    rejected

/-- The computed reachability bound suffices for a single exact finite-carrier
comparison. Matched faults keep their actual final state. -/
theorem Table.checkEntries_cutoff_iff (checked : g.checkNative raw = true) (checked' : h.checkNative raw' = true) :
    let n := g.cutoff h callers decodeLeft decodeRight replies left right
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      ∀ (input : Payload A) (prim : Primitives Φ n) (s : Fin n),
        Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings (decodeLeft input))) s ≤
          Shape.denote (withExitUB raw' h.selected) (model prim (h.visible.bindings (decodeRight input))) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.cutoff_iff
    checked checked'

/-- Success is exact for arbitrary deterministic stores at the original
packed endpoints, once both exact readbacks have succeeded. -/
theorem Table.checkEntries_accepts_iff (checked : g.checkNative raw = true) (checked' : h.checkNative raw' = true) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.accepts_iff
    checked checked'

/-- On admitted originals, rejection is exactly failure of arbitrary-store
deterministic refinement. -/
theorem Table.checkEntries_rejects_iff (checked : g.checkNative raw = true) (checked' : h.checkNative raw' = true) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false ↔
      ¬ g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.rejects_iff
    checked checked'

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
