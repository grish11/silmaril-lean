module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Reachable.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Reachable

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (Typed withExitUB)
open Syntax (Payload Primitives StatePrimitives)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {A : Syntax.Ty} {g : Endpoint S R A} {h : Endpoint S T A}
  {a : Payload (R.get g.control.entry)} {b : Payload (T.get h.control.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

variable {raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A)}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.control.entry] (Exits A)} {results : Nat}
  {codec : Fin results ≃ Packet (Exits A)}

/-- The reachable cutoff is sound in every store universe. -/
theorem Endpoint.checkReachable_sound {σ : Type v} (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (yes : g.checkReachable? h raw raw' codec a b replies left right = some true)
    (prim : StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.control.selected) (Syntax.model prim (g.control.bindings a)) s ≤
      Shape.denote (withExitUB raw' h.control.selected) (Syntax.model prim (h.control.bindings b)) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.Reachable.accepts_sound
    hg hh yes prim s

/-- Exact readback on both endpoints makes the finite reachable-cutoff verdict
decisive over arbitrary deterministic stores. -/
theorem Endpoint.checkReachable_accepts_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.checkReachable? h raw raw' codec a b replies left right = some true ↔
      ∀ (σ : Type) (prim : StatePrimitives Φ σ) (s : σ),
        Shape.denote (withExitUB raw g.control.selected) (Syntax.model prim (g.control.bindings a)) s ≤
          Shape.denote (withExitUB raw' h.control.selected) (Syntax.model prim (h.control.bindings b)) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.Reachable.accepts_iff hg hh

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
