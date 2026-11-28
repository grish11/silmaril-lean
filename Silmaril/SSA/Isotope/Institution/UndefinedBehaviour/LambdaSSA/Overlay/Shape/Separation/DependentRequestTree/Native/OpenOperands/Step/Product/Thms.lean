module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Observer.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Observation.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Soundness

/-! # Soundness of closed finite relations for native guarded feedback -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open Payload (Endpoint)
open TwoRequest (Tag)
open CFG.Dependent.Native (withExitUB)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {σ : Type v}

theorem Head.checkPair_iff [DecidableEq Φ] (replies : ReplyEnumeration S)
    (related : Packet R → Packet T → Bool) (p : Head S R) (q : Head S T) :
    p.checkPair replies related q = true ↔ p.Matches (fun x y => related x y = true) q :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.check_pair_iff
    replies related p q

theorem productContains_iff (pairs : List (Packet R × Packet T)) (p : Packet R) (q : Packet T) :
    productContains pairs p q = true ↔ (p, q) ∈ pairs :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.product_contains_iff
    pairs p q

/-- The selection bit recorded by a terminal head is the original tag's mark. -/
theorem Table.head_mark (g : Table S R) (caller : Syntax.Payload (R.get g.entry)) (p : Packet R)
    {i : Tag} {marked : Bool} (head : g.head caller p = .exit i marked) : g.selected i = marked :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.head_mark g caller p head

theorem HeadObserver.closed_relation_sound (g : HeadObserver.{u,v} S R) (h : HeadObserver.{u,v} S T)
    (prim : Syntax.StatePrimitives Φ σ) (rel : Packet R → Packet T → Prop)
    (closed : ∀ p q, rel p q → (g.head p).MatchesWith
      (fun i j => (i, g.returnValue p i) = (j, h.returnValue q j)) rel (h.head q))
    {p : Packet R} {q : Packet T} (related : rel p q) (s : σ) :
    g.observe prim p s ≤ h.observe prim q s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.observer_closed_relation_sound
    g h prim rel closed related s

/-- Shared request closure preserves complete ordered outputs and matches
infinite replay as ordinary divergence. -/
theorem Payload.Endpoint.closed_relation_sound {A : Syntax.Ty} (g : Endpoint S R A) (h : Endpoint S T A)
    (caller : Syntax.Payload (R.get g.control.entry)) (caller' : Syntax.Payload (T.get h.control.entry))
    (prim : Syntax.StatePrimitives Φ σ) (rel : Packet R → Packet T → Prop)
    (closed : ∀ p q, rel p q → (g.control.head caller p).MatchesWith
      (fun i j => (g.returnPacket caller p i).raw = (h.returnPacket caller' q j).raw) rel (h.control.head caller' q))
    {p : Packet R} {q : Packet T} (related : rel p q) (s : σ) :
    g.observeAt caller prim p s ≤ h.observeAt caller' prim q s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.payload_closed_relation_sound g h caller caller' prim rel closed related s

/-- A genuine infinite sequence of guarded replies has the ordinary divergence observation. -/
theorem Payload.Endpoint.observe_infinite {A : Syntax.Ty} (g : Endpoint S R A)
    (caller : Syntax.Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ)
    (configs : Nat → Packet R) (store : Nat → σ)
    (next : ∀ n, (g.control.head caller (configs n)).execute prim (store n) =
      .repeat (configs (n + 1)) (store (n + 1))) :
    g.observeAt caller prim (configs 0) (store 0) = WithTop.some {Outcome.diverge} :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.payload_observe_infinite g caller prim configs store next

theorem Payload.Endpoint.unit_matches_iff (g : Table S R) (h : Table S T) (a : Syntax.Payload (R.get g.entry))
    (b : Syntax.Payload (T.get h.entry)) (p : Packet R) (q : Packet T) (rel : Packet R → Packet T → Prop)
    (lower : Head S R) (upper : Head S T) :
    lower.MatchesWith
      (fun i j => ((Endpoint.unit g).returnPacket a p i).raw = ((Endpoint.unit h).returnPacket b q j).raw)
      rel upper ↔ lower.Matches rel upper :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.unit_matches_iff g h a b p q rel lower upper

/-- A closed relation gives refinement at every related pair and common
initial state. The infinite case uses native feedback's ordinary divergence. -/
theorem Table.closed_relation_sound (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (prim : Syntax.StatePrimitives Φ σ) (rel : Packet R → Packet T → Prop)
    (closed : ∀ p q, rel p q → (g.head caller p).Matches rel (h.head caller' q))
    {p : Packet R} {q : Packet T} (related : rel p q) (s : σ) :
    g.observeAt caller prim p s ≤ h.observeAt caller' prim q s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.closed_relation_sound
    g h caller caller' prim rel closed related s

/-- Acceptance, together with exact native readback, proves refinement of
the original decorated runners for each deterministic shaped interpreter. -/
theorem Table.checkProduct_sound [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (readback : g.checkNative raw = true) (readback' : h.checkNative raw' = true)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (pairs : List (Packet R × Packet T))
    (checked : g.checkProduct h caller caller' replies pairs = true)
    (prim : Syntax.StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings caller)) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings caller')) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.product_sound
    g h raw raw' readback readback' caller caller' replies pairs checked prim s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
