module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.SingleRequest.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Native
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest

open Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational (Model)
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (bind_assoc bind_congr return_bind)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (observe_request replyOutcomes fault_bind diverge_bind)

universe v w

private def replyExpr (forward : Bool) : Syntax.Expr [U] U :=
  if forward then .var 0 else .unit

private theorem observe_jump (M : Model.{0,v,w} Instr 0) (i : Fin Exits.length)
    (forward : Bool) (a : Value M.α) (s : M.σ) :
    denote (.native (Native.jump i (exit_type i) (replyExpr forward))) (extendModel M a) s =
      WithTop.some {Outcome.ret i (if forward then a else .unit) s} := by
  apply congrArg WithTop.some
  ext o
  rw [mem_nativeOutcomes_iff _ ((envOfBound_agrees M.bound).extend a), Set.mem_singleton_iff]
  cases o with
  | ret j b t =>
    have invert {label : Nat} {v : Value M.α} {final : M.σ}
        (run : Region.Eval M.instr (extend (envOfBound M.bound) a)
          (.br i.val ((replyExpr forward).term (Φ := Instr))) s label v final) :
        label = i.val ∧ v = (if forward then a else .unit) ∧ final = s := by
      cases forward <;> cases run with | br value => cases value; exact ⟨rfl, rfl, rfl⟩
    constructor
    · intro run
      obtain ⟨label, value, final⟩ := invert run
      exact (Outcome.ret.injEq ..).mpr ⟨Fin.ext label, value, final⟩
    · intro eq
      obtain ⟨rfl, rfl, rfl⟩ := Outcome.ret.inj eq
      cases forward
      · exact .br .unit
      · exact .br .var
  | fault t =>
    constructor
    · intro run
      cases forward <;> cases run with | br arg => cases arg
    · intro eq
      cases eq
  | diverge =>
    constructor
    · intro run
      cases forward <;> cases run.unfold with
      | br arg => cases arg
      | core step => cases step
    · intro eq
      cases eq

theorem denote_endpoint (p : Endpoint) (M : Model.{0,v,w} Instr 0) (s : M.σ) :
    denote p.region M s =
      (denote (.native request) M s).bind (fun _ a t => p.afterReply a t) := by
  let k (i : Fin [U].length) : Native.Typed Instr ([U].get i :: []) Exits := by
    obtain rfl := Fin.eq_zero i
    exact p.router
  let h (i : Fin Exits.length) a t :=
    denote (Native.exitContinuation (Γ := []) (Φ := Instr) p.selected i) (extendModel M a) t
  change (denote (.native (Native.bind request p.router)) M s).bind h = _
  change (denote (.native ⟨nativeLsubst request k, nativeLsubst_hasType request k⟩) M s).bind h = _
  rw [← denote_native_lsubst request k M s]
  change ((denote (.native request) M s).bind
    (fun i a t => denote (.native (k i)) (extendModel M a) t)).bind h = _
  rw [bind_assoc]
  congr 1
  funext i a t
  obtain rfl := Fin.eq_zero i
  change (denote (.native p.router) (extendModel M a) t).bind h = p.afterReply a t
  change (denote (.native (Native.jump (L := Exits) p.exit (exit_type p.exit) (replyExpr p.forward)))
    (extendModel M a) t).bind h = _
  rw [observe_jump, return_bind]
  unfold h Native.exitContinuation Endpoint.afterReply
  rw [show p.selected p.exit = p.ub by simp [Endpoint.selected]]
  cases hp : p.ub
  · simp only [Bool.false_eq_true, ↓reduceIte]
    let b := if p.forward then a else .unit
    generalize p.exit = i
    fin_cases i <;> exact observe_jump M _ true b t
  · rfl

private theorem denote_unit (p : Endpoint) (M : Shape.Model.{0,0,v,w} Instr []) (s : M.raw.σ) :
    Shape.denote p.region M s =
      (denote (.native request) M.raw s).bind (fun _ _ t => p.afterReply .unit t) := by
  change denote p.region M.raw s = _
  rw [denote_endpoint]
  refine bind_congr fun i a t reply => ?_
  have typed : Shape.ValueTyped M.atomType a ([U].get i) :=
    Shape.returns_typed (.native request) M s reply
  obtain rfl := Fin.eq_zero i
  cases typed
  rfl

private theorem afterReply_unit_le_iff {α : Type v} {σ : Type w} (p q : Endpoint) (t : σ) :
    p.afterReply (.unit : Value α) t ≤ q.afterReply .unit t ↔ ReplyRefines p q := by
  cases hp : p.ub <;> cases hq : q.ub <;>
    simp [Endpoint.afterReply, ReplyRefines, hp, hq, WithTop.coe_le_coe]

theorem shaped_sound (p q : Endpoint) (le : ReplyRefines p q)
    (M : Shape.Model.{0,0,v,w} Instr []) (s : M.raw.σ) :
    Shape.denote p.region M s ≤ Shape.denote q.region M s := by
  rw [denote_unit, denote_unit]
  exact Behaviour.bind_mono le_rfl (fun _ _ t => (afterReply_unit_le_iff p q t).mpr le)

theorem finite_observe {states : Nat} (p : Endpoint) (prim : Syntax.Primitives Instr states)
    (s : Fin states) :
    Shape.denote p.region (Syntax.model prim Syntax.emptyBindings) s =
      match prim .request ⟨.unit, .unit⟩ s with
      | .ret a t => p.afterReply a.val t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} := by
  let M := Syntax.model prim Syntax.emptyBindings
  change denote p.region M.raw s = _
  rw [denote_endpoint, show denote (.native request) M.raw s =
    WithTop.some (replyOutcomes (prim .request ⟨.unit, .unit⟩ s)) from
    observe_request prim Syntax.emptyBindings Instr.request .unit s]
  cases prim .request ⟨.unit, .unit⟩ s with
  | ret a t => exact return_bind 0 a.val t _
  | fault t => exact fault_bind t _
  | diverge => exact diverge_bind _

theorem finite_test_iff (p q : Endpoint) :
    let M := Syntax.model (unitInterpreter (1 : Fin 2)) Syntax.emptyBindings
    Shape.denote p.region M 0 ≤ Shape.denote q.region M 0 ↔ ReplyRefines p q := by
  dsimp only
  rw [finite_observe, finite_observe]
  exact afterReply_unit_le_iff p q (1 : Fin 2)

private theorem raw_request :
    denote (.native request) rawProbe 0 =
      WithTop.some {Outcome.ret 0 (.inl Value.unit) (1 : Fin 2)} := by
  apply congrArg WithTop.some
  ext o
  rw [mem_nativeOutcomes_iff _ (envOfBound_agrees rawProbe.bound), Set.mem_singleton_iff]
  cases o with
  | ret i b t =>
    obtain rfl := Fin.eq_zero i
    constructor
    · intro run
      cases run with
      | br arg =>
        cases arg with
        | op _ reply =>
          exact (Outcome.ret.injEq ..).mpr ⟨rfl, reply.1, reply.2⟩
    · intro eq
      obtain ⟨_, rfl, rfl⟩ := Outcome.ret.inj eq
      exact .br (.op .unit ⟨rfl, rfl⟩)
  | fault t =>
    constructor
    · intro run
      cases run with
      | br arg =>
        cases arg with
        | op_arg failed => cases failed
        | op_fault _ failed => exact failed.elim
    · intro eq
      cases eq
  | diverge =>
    constructor
    · intro run
      cases run.unfold with
      | br arg =>
        cases arg with
        | op_arg failed => cases failed
        | primitive _ failed => exact failed.elim
      | core step => cases step
    · intro eq
      cases eq

private theorem afterReply_raw_le (p q : Endpoint) (le : RawReplyRefines p q)
    {α : Type v} {σ : Type w} (a : Value α) (t : σ) :
    p.afterReply a t ≤ q.afterReply a t := by
  rcases le with h | ⟨hp, i, forward⟩
  · simp [Endpoint.afterReply, h]
  · by_cases hq : q.ub = true
    · simp [Endpoint.afterReply, hq]
    · simp [Endpoint.afterReply, hp, hq, i, forward]

theorem raw_sound (p q : Endpoint) (h : RawReplyRefines p q) :
    Refines.{0,0,v,w} p.region q.region := by
  intro M s
  rw [denote_endpoint, denote_endpoint]
  exact Behaviour.bind_mono le_rfl (fun _ a t => afterReply_raw_le p q h a t)

theorem raw_test_iff (p q : Endpoint) :
    denote p.region rawProbe 0 ≤ denote q.region rawProbe 0 ↔ RawReplyRefines p q := by
  rw [denote_endpoint, denote_endpoint, raw_request, return_bind, return_bind]
  cases hp : p.ub <;> cases hq : q.ub <;> cases hf : p.forward <;> cases hg : q.forward <;>
    simp [Endpoint.afterReply, RawReplyRefines, hp, hq, hf, hg, WithTop.coe_le_coe]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest
