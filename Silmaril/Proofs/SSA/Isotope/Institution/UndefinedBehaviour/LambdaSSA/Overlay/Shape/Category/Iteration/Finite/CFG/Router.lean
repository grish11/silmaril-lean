module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Native
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (observe_branch observe_case denote_push fault_bind diverge_bind)

universe u x

variable {σ : Type x}
variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)] {states : Nat}
variable {Γ L : List (Silmaril.Ty Empty)} {X A B : (Silmaril.Ty Empty)} {n : Nat}

theorem observe_jump (prim : StatePrimitives Φ σ) (env : Bindings Γ) (i : Fin L.length)
    (typed : L.get i = A) (a : Expr Γ A) (s : σ) :
    denote (jump (Φ := Φ) i typed a) (model prim env).raw s =
      WithTop.some {Outcome.ret i (a.eval env).val s} := by
  subst A
  exact observe_branch prim env i a s

theorem observe_select (prim : StatePrimitives Φ σ) (env : Bindings Γ)
    (p : Payload (.coprod A B))
    (left : Region Φ (A :: .coprod A B :: Γ) L) (right : Region Φ (B :: .coprod A B :: Γ) L)
    (s : σ) :
    denote (select left right) (model prim (env.push p)).raw s =
      match splitPayload p with
      | .inl a => denote left (model prim ((env.push p).push a)).raw s
      | .inr b => denote right (model prim ((env.push p).push b)).raw s := by
  rw [select, denote]
  erw [observe_case prim (env.push p) (.var 0) s]
  change Behaviour.bind (match splitPayload p with
    | .inl a => WithTop.some {Outcome.ret (0 : Fin 2) a.val s}
    | .inr b => WithTop.some {Outcome.ret (1 : Fin 2) b.val s}) _ = _
  cases splitPayload p with
  | inl a => exact (return_bind 0 a.val s _).trans (denote_push prim (env.push p) a left s)
  | inr b => exact (return_bind 1 b.val s _).trans (denote_push prim (env.push p) b right s)

private theorem observe_routePacket (prim : Primitives Φ states) (env : Bindings Γ)
    (fallback : Fin L.length) (target : Fin n → Fin L.length)
    (typed : ∀ j, L.get (target j) = A) (p : Payload (Packet A n)) (s : Fin states) :
    denote (routePacket fallback target typed) (model prim (env.push p)).raw s =
      WithTop.some {Outcome.ret (target (unpack p).1) (unpack p).2.val s} := by
  induction n generalizing Γ with
  | zero => exact (noEmptyPayload p).elim
  | succ n ih =>
    rw [routePacket]
    erw [observe_select prim env p _ _ s]
    cases h : splitPayload p with
    | inl a =>
      simp only [unpack, h]
      exact observe_jump prim ((env.push p).push a) (target 0) (typed 0) (.var 0) s
    | inr a =>
      simp only [unpack, h]
      exact ih (env.push p) (fun j => target j.succ) (fun j => typed j.succ) a

private theorem observe_route (prim : Primitives Φ states) (env : Bindings Γ)
    (p : Payload (.coprod B (Packet A n))) (s : Fin states) :
    denote (route A B n) (model prim (env.push p)).raw s =
      match splitPayload p with
      | .inl b => WithTop.some {Feedback.external (labels A n) [B] (Outcome.ret 0 b.val s)}
      | .inr a => WithTop.some (Set.singleton
          (Outcome.ret (Feedback.internal (labels A n) [B] (label (unpack a).1)) (unpack a).2.val s)) := by
  rw [route]
  erw [observe_select prim env p _ _ s]
  cases splitPayload p with
  | inl b => exact observe_jump prim ((env.push p).push b) (exitLabel A B n) external_type (.var 0) s
  | inr a => exact observe_routePacket prim (env.push p) _ _ _ a s

@[expose] def positionalAnswer (answer : Answer (.coprod B (Packet A n)) states) :
    Behaviour (labels A n ++ [B]).length Unit (Fin states) :=
  match answer with
  | .ret p t =>
    match splitPayload p with
    | .inl b => WithTop.some {Feedback.external (labels A n) [B] (Outcome.ret 0 b.val t)}
    | .inr a => WithTop.some (Set.singleton
        (Outcome.ret (Feedback.internal (labels A n) [B] (label (unpack a).1)) (unpack a).2.val t))
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}
  | .ub => ⊤

private theorem observe_cast (prim : Primitives Φ states) (env : Bindings Γ) (p : Payload A)
    {A' : (Silmaril.Ty Empty)} (h : A' = A) (r : Region Φ (A :: Γ) L) (s : Fin states) :
    denote (castHead h r) (extendModel (model prim env).raw p.val) s =
      denote r (model prim (env.push p)).raw s := by
  cases h
  exact denote_push prim env p r s

theorem observe_bindOne (prim : Primitives Φ states) (env : Bindings Γ)
    (body : Program Φ Γ A) (k : Region Φ (A :: Γ) L) (s : Fin states) :
    denote (bindOne body.region k) (model prim env).raw s =
      match body.eval prim env s with
      | .ret p t => denote k (model prim (env.push p)).raw t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge}
      | .ub => ⊤ := by
  rw [bindOne, denote]
  erw [Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax.observe_eval prim body env s]
  cases body.eval prim env s with
  | ub => exact Behaviour.top_bind _
  | diverge => exact diverge_bind _
  | fault t => exact fault_bind t _
  | ret p t =>
    exact (return_bind (0 : Fin 1) p.val t _).trans (denote_push prim env p k t)

theorem observe_routed (cfg : Blocks Φ X A B n) (prim : Primitives Φ states)
    (i : Fin (labels A n).length) (env : Bindings [X]) (a : Payload A) (s : Fin states) :
    denote (cfg.routed i) (extendModel (model prim env).raw a.val) s =
      positionalAnswer ((cfg.block (blockIndex i)).eval prim (env.push a) s) := by
  rw [Blocks.routed, observe_cast, observe_bindOne]
  cases (cfg.block (blockIndex i)).eval prim (env.push a) s with
  | ub | diverge | fault => rfl
  | ret p t => exact observe_route prim (env.push a) p t

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG
