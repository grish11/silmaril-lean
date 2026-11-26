module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Native
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category (returnPayload splitPayload pairPayload iterateCaptured)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)

universe u w x

variable {σ : Type x}
variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)] {states : Nat} {Γ : List (Silmaril.Ty Empty)}
variable {X A B : Silmaril.Ty Empty} {captures seeds results : Nat}

private theorem push_values (env : Bindings Γ) (a : Payload A) :
    LetIter.Semantics.extend (fun i => (env i).val) a.val = fun i => (env.push a i).val := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem denote_push (prim : StatePrimitives Φ σ) (env : Bindings Γ) (a : Payload A)
    {L : List (Silmaril.Ty Empty)} (body : Region Φ (A :: Γ) L) (s : σ) :
    denote body (extendModel (model prim env).raw a.val) s =
      denote body (model prim (env.push a)).raw s := by
  let run (bound : Fin (Γ.length + 1) → Value Unit) : Behaviour L.length Unit (σ) :=
    denote body (rawModel prim bound) s
  exact congrArg run (push_values env a)

theorem fault_bind {α : Type w} {σ : Type x} {n m : Nat} (s : σ)
    (k : Fin n → Value α → σ → Behaviour m α σ) :
    Behaviour.bind (WithTop.some ({Outcome.fault s} : Set (Outcome n α σ))) k = WithTop.some {Outcome.fault s} := by
  simp [Behaviour.bind, Behaviour.possible, WithTop.untopD_coe]
  ext o
  cases o <;> simp [Outcome.bind]

theorem diverge_bind {α : Type w} {σ : Type x} {n m : Nat}
    (k : Fin n → Value α → σ → Behaviour m α σ) :
    Behaviour.bind (WithTop.some ({Outcome.diverge} : Set (Outcome n α σ))) k = WithTop.some {Outcome.diverge} := by
  simp [Behaviour.bind, Behaviour.possible, WithTop.untopD_coe]
  ext o
  cases o <;> simp [Outcome.bind]

theorem observe_eval (prim : Primitives Φ states) (body : Program Φ Γ A) (env : Bindings Γ) (s : Fin states) :
    denote body.region (model prim env).raw s = (body.eval prim env s).behaviour := by
  induction body generalizing s with
  | ret arg => exact observe_return prim env arg s
  | ub => rfl
  | call f arg body ih =>
    rw [Program.region, denote, observe_request, Program.eval]
    cases prim f (arg.eval env) s with
    | ret a t =>
      refine (return_bind (0 : Fin 1) a.val t _).trans ?_
      exact (denote_push prim env a body.region t).trans (ih (env.push a) t)
    | fault t => exact fault_bind t _
    | diverge => exact diverge_bind _
  | case arg left right ihl ihr =>
    rw [Program.region, denote, observe_case, Program.eval]
    cases splitPayload (arg.eval env) with
    | inl a =>
      refine (return_bind 0 a.val s _).trans ?_
      exact (denote_push prim env a left.region s).trans (ihl (env.push a) s)
    | inr b =>
      refine (return_bind 1 b.val s _).trans ?_
      exact (denote_push prim env b right.region s).trans (ihr (env.push b) s)

theorem row_behaviour (codes : Codes X A B captures seeds results) (prim : Primitives Φ states)
    (answer : Answer (.coprod B A) states) :
    (answer.row codes).behaviour (codes.carrier prim) = answer.behaviour := by
  cases answer with
  | fault | diverge | ub => rfl
  | ret a t =>
    obtain ⟨value, typed⟩ := a
    cases typed with
    | inl typed =>
      change returnPayload (.inl (codes.result (codes.result.symm ⟨_, typed⟩)).val) t =
        returnPayload (.inl _) t
      rw [Equiv.apply_symm_apply]
    | inr typed =>
      let a : Payload A := ⟨_, typed⟩
      change (let p := finProdFinEquiv.symm (finProdFinEquiv (codes.seed.symm a, t))
              returnPayload (.inr (codes.seed p.1).val) p.2) = returnPayload (.inr a.val) t
      simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem generate_certified (codes : Codes X A B captures seeds results) (prim : Primitives Φ states)
    (body : Program Φ [A, X] (.coprod B A)) :
    Certified (codes.carrier prim) body.region (generate codes prim body) := by
  intro c p
  let env := emptyBindings.push (codes.capture c)
  let start := (codes.carrier prim).invocation p
  calc
    _ = denote body.region (model prim (env.push start.1)).raw start.2 := by
      have boundEq : LetIter.Semantics.extend
          (LetIter.Semantics.extend (fun i => (emptyBindings i).val) (codes.capture c).val)
          start.1.val = (fun i => (env.push start.1 i).val) := by
        rw [push_values emptyBindings (codes.capture c)]
        exact push_values env start.1
      let run (bound : Fin 2 → Value Unit) : Behaviour 1 Unit (Fin states) :=
        denote body.region (rawModel prim bound) start.2
      exact congrArg run boundEq
    _ = _ := (observe_eval prim body (env.push start.1) start.2).trans
      (row_behaviour codes prim (body.eval prim (env.push start.1) start.2)).symm

theorem check_generate_iff (codes : Codes X A B captures seeds results) (prim : Primitives Φ states)
    (lower upper : Program Φ [A, X] (.coprod B A)) :
    check (generate codes prim lower) (generate codes prim upper) = true ↔
      ∀ (c : Fin captures) (a : Payload A) (s : Fin states),
        (iterateCaptured (model prim emptyBindings) lower.region).run 0
          (pairPayload (codes.capture c) a) s ≤
        (iterateCaptured (model prim emptyBindings) upper.region).run 0
          (pairPayload (codes.capture c) a) s := by
  rw [check_iff (codes.carrier prim) _ _ (generate_certified codes prim lower)
    (generate_certified codes prim upper)]
  constructor
  · intro checked c a s
    let p := finProdFinEquiv (codes.seed.symm a, s)
    have decoded : (codes.carrier prim).invocation p = (a, s) := by
      change (let q := finProdFinEquiv.symm (finProdFinEquiv (codes.seed.symm a, s))
              (codes.seed q.1, q.2)) = _
      simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    have captured : (codes.carrier prim).capture c = codes.capture c := rfl
    simpa only [decoded, captured] using checked c p
  · intro all c p
    exact all c ((codes.carrier prim).invocation p).1 ((codes.carrier prim).invocation p).2

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
