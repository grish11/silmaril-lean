module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Router
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Native
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category (splitPayload noEmptyPayload)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG (bindOne castHead)
open Silmaril.Isotope.LambdaSSA.Region (packedExitType)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG
  (observe_jump observe_select observe_bindOne)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (denote_push fault_bind diverge_bind)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (observe_request)

universe u x

variable {σ : Type x}
variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)] {states : Nat} {X : Silmaril.Ty Empty}
variable {Γ P R L : List (Silmaril.Ty Empty)}

private theorem observe_routePacket (prim : StatePrimitives Φ σ) (env : Bindings Γ)
    (target : Fin P.length → Fin L.length) (typed : ∀ j, L.get (target j) = P.get j)
    (p : Packed P) (s : σ) :
    denote (routePacket target typed) (model prim (env.push p)).raw s =
      WithTop.some {Outcome.ret (target (unpack p).1) (unpack p).2.val s} := by
  induction P generalizing Γ with
  | nil => exact (noEmptyPayload p).elim
  | cons A P ih =>
    rw [routePacket]
    erw [observe_select prim env p _ _ s]
    cases h : splitPayload p with
    | inl a =>
      have decoded : unpack p = ⟨0, a⟩ := by rw [unpack, h]
      rw [decoded]
      exact observe_jump prim ((env.push p).push a) (target 0) (typed 0) (.var 0) s
    | inr a =>
      have decoded : unpack p = ⟨(unpack a).1.succ, (unpack a).2⟩ := by rw [unpack, h]
      rw [decoded]
      exact ih (env.push p) (fun j => target j.succ) (fun j => typed j.succ) a

private theorem cast_packet {A B : Syntax.Ty} (typed : A = B) (prim : StatePrimitives Φ σ)
    (env : Bindings Γ) (a : Payload A) (r : Region Φ (B :: Γ) L) (s : σ) :
    denote (castHead typed r) (model prim (env.push a)).raw s =
      denote r (model prim (env.push (cast (congrArg Syntax.Payload typed) a))).raw s := by
  cases typed
  rfl

theorem observe_packedRequestTo (prim : StatePrimitives Φ σ) (env : Bindings Γ)
    (f : Φ) (arg : Expr Γ (instrSrc f)) (typed : instrTrg f = packedExitType R)
    (target : Fin R.length → Fin L.length) (routed : ∀ i, L.get (target i) = R.get i)
    (s : σ) :
    denote (packedRequestTo f arg typed target routed) (model prim env).raw s =
      match prim f (arg.eval env) s with
      | .ret a t =>
        let p := unpack (cast (congrArg Syntax.Payload typed) a)
        WithTop.some {Outcome.ret (target p.1) p.2.val t}
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} := by
  rw [packedRequestTo, bindOne, denote]
  erw [observe_request prim env f arg s]
  cases prim f (arg.eval env) s with
  | ret a t =>
    refine (return_bind (0 : Fin 1) a.val t _).trans ?_
    rw [denote_push, cast_packet]
    exact observe_routePacket prim env target routed (cast (congrArg Syntax.Payload typed) a) t
  | fault t => exact fault_bind t _
  | diverge => exact diverge_bind _

theorem observe_packedRequest_bind (prim : Primitives Φ states)
    (env : Bindings Γ) (f : Φ) (arg : Expr Γ (instrSrc f)) (typed : instrTrg f = packedExitType R)
    (k : (i : Fin R.length) → Region Φ (R.get i :: Γ) L) (s : Fin states) :
    Shape.denote (.lsubst (packedRequest f arg typed) k) (model prim env) s =
      match prim f (arg.eval env) s with
      | .ret a t =>
        let p := unpack (cast (congrArg Syntax.Payload typed) a)
        Shape.denote (k p.1) (model prim (env.push p.2)) t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} := by
  change (denote (packedRequest f arg typed) (model prim env).raw s).bind _ = _
  unfold packedRequest
  rw [observe_packedRequestTo]
  cases prim f (arg.eval env) s with
  | ret a t =>
    let p := unpack (cast (congrArg Syntax.Payload typed) a)
    exact (return_bind p.1 p.2.val t _).trans (denote_push prim env p.2 (k p.1) t)
  | fault t => exact fault_bind t _
  | diverge => exact diverge_bind _

@[expose] def routedAnswer (answer : Answer (.coprod (packedExitType L) (packedExitType R)) states) :
    Behaviour (R ++ L).length Unit (Fin states) :=
  match answer with
  | .ret p t =>
    match splitPayload p with
    | .inl b =>
      let out := unpack b
      WithTop.some {Feedback.external R L (Outcome.ret out.1 out.2.val t)}
    | .inr a =>
      let out := unpack a
      WithTop.some {Outcome.ret (Feedback.internal R L out.1) out.2.val t}
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}
  | .ub => ⊤

private theorem observe_route (prim : Primitives Φ states) (env : Bindings Γ)
    (p : Payload (.coprod (packedExitType L) (packedExitType R))) (s : Fin states) :
    denote (route R L) (model prim (env.push p)).raw s = routedAnswer (.ret p s) := by
  rw [route]
  erw [observe_select prim env p _ _ s]
  simp only [routedAnswer]
  cases splitPayload p with
  | inl b => exact observe_routePacket prim (env.push p) (exitLabel R L) external_type b s
  | inr a => exact observe_routePacket prim (env.push p) (Feedback.internal R L) internal_type a s

theorem observe_routed (g : Blocks Φ X R L) (prim : Primitives Φ states) (i : Fin R.length)
    (env : Bindings [X]) (a : Payload (R.get i)) (s : Fin states) :
    denote (g.routed i) (extendModel (model prim env).raw a.val) s =
      routedAnswer ((g.block i).eval prim (env.push a) s) := by
  rw [Blocks.routed, denote_push prim env a, observe_bindOne]
  cases (g.block i).eval prim (env.push a) s with
  | ub | diverge | fault => rfl
  | ret p t => exact observe_route prim (env.push a) p t

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
