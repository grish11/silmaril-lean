module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Probe

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet)
open Payload (Endpoint)
open Syntax (Payload Primitives)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty} {A : Syntax.Ty}

/-- A failed local head match has a separating terminal test at one available store. -/
theorem HeadObserver.local_mismatch_refutes [DecidableEq Φ] (g : HeadObserver.{u,0} S R) (h : HeadObserver.{u,0} S T)
    (p : Packet R) (q : Packet T)
    (fuel : Nat) (mismatch : ¬ (g.head p).MatchesWith
      (fun i j => (i, g.returnValue p i) = (j, h.returnValue q j)) (fun _ _ => True) (h.head q)) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observe prim p 0 ≤ h.observe prim q 0 :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.observer_local_mismatch_refutes
    g h p q fuel mismatch

theorem HeadObserver.prepend_refutation [DecidableEq Φ] (g : HeadObserver.{u,0} S R) (h : HeadObserver.{u,0} S T)
    (p : Packet R) (q : Packet T) {f : Φ} {arg : Payload (instrSrc f)}
    {next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R}
    {route : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T}
    (lower : g.head p = .request f arg next) (upper : h.head q = .request f arg route)
    (answer : Packet (S.replies f))
    {fuel : Nat} (other : Primitives Φ fuel) (t : Fin fuel)
    (bad : ¬ g.observe other (next answer.1 answer.2) t ≤ h.observe other (route answer.1 answer.2) t) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observe prim p 0 ≤ h.observe prim q 0 :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.observer_prepend_refutation
    g h p q lower upper answer other t bad

theorem local_mismatch_refutes [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry)) (p : Packet R) (q : Packet T)
    (fuel : Nat) (mismatch : ¬ (g.head a p).Matches (fun _ _ => True) (h.head b q)) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.local_mismatch_refutes g h a b p q fuel mismatch

/-- A fresh store issues the shared reply and enters the embedded suffix interpreter. -/
theorem prepend_refutation [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry))
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (p : Packet R) (q : Packet T) {f : Φ} {arg : Payload (instrSrc f)}
    {next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R}
    {route : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T}
    (lower : g.head a p = .request f arg next) (upper : h.head b q = .request f arg route)
    (answer : Packet (S.replies f))
    {fuel : Nat} (other : Primitives Φ fuel) (t : Fin fuel)
    (bad : ¬ g.observeAt a other (next answer.1 answer.2) t ≤ h.observeAt b other (route answer.1 answer.2) t) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.prepend_refutation
    g h a b left right p q lower upper answer other t bad

theorem Payload.Endpoint.local_mismatch_refutes [DecidableEq Φ] (g : Endpoint S R A) (h : Endpoint S T A)
    (a : Payload (R.get g.control.entry)) (b : Payload (T.get h.control.entry)) (p : Packet R) (q : Packet T)
    (fuel : Nat) (mismatch : ¬ (g.control.head a p).MatchesWith
      (fun i j => (g.returnPacket a p i).raw = (h.returnPacket b q j).raw) (fun _ _ => True) (h.control.head b q)) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.payload_local_mismatch_refutes g h a b p q fuel mismatch

theorem Payload.Endpoint.prepend_refutation [DecidableEq Φ] (g : Endpoint S R A) (h : Endpoint S T A)
    (a : Payload (R.get g.control.entry)) (b : Payload (T.get h.control.entry))
    (p : Packet R) (q : Packet T) {f : Φ} {arg : Payload (instrSrc f)}
    {next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R}
    {route : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T}
    (lower : g.control.head a p = .request f arg next) (upper : h.control.head b q = .request f arg route)
    (answer : Packet (S.replies f))
    {fuel : Nat} (other : Primitives Φ fuel) (t : Fin fuel)
    (bad : ¬ g.observeAt a other (next answer.1 answer.2) t ≤ h.observeAt b other (route answer.1 answer.2) t) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.payload_prepend_refutation g h a b p q lower upper answer other t bad

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
