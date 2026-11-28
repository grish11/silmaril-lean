module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind bind_top_iff)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (fault_bind diverge_bind denote_push)

universe v w

variable {Γ : List (Silmaril.Ty Empty)}

private theorem request_ret (M : Shape.Model.{0,0,v,w} Instr Γ) (f : Instr) (s t : M.raw.σ)
    (i : Tag) (a : Value M.raw.α) :
    Region.Eval M.raw.instr (envOfBound M.raw.bound) (request f Γ).val s i.val a t ↔
      a = .unit ∧ M.raw.instr f .unit s (bitValue i) t := by
  constructor
  · have classify {label : Nat} (run : Region.Eval M.raw.instr (envOfBound M.raw.bound)
        (request f Γ).val s label a t) :
        ∃ j : Tag, label = j.val ∧ a = .unit ∧ M.raw.instr f .unit s (bitValue j) t := by
      cases run with
      | case_inl head branch =>
        cases branch with
        | br term =>
          cases term
          cases head with
          | op arg reply =>
            cases arg
            have typed := M.instrTyped .unit reply
            cases typed with
            | inl b => cases b; exact ⟨0, rfl, rfl, reply⟩
      | case_inr head branch =>
        cases branch with
        | br term =>
          cases term
          cases head with
          | op arg reply =>
            cases arg
            have typed := M.instrTyped .unit reply
            cases typed with
            | inr b => cases b; exact ⟨1, rfl, rfl, reply⟩
    intro run
    obtain ⟨j, label, value, step⟩ := classify run
    rw [Fin.ext label]
    exact ⟨value, step⟩
  · rintro ⟨rfl, h⟩
    fin_cases i
    · exact .case_inl (.op .unit h) (.br .unit)
    · exact .case_inr (.op .unit h) (.br .unit)

private theorem request_fault (M : Shape.Model.{0,0,v,w} Instr Γ) (f : Instr) (s t : M.raw.σ) :
    Region.Fault M.raw.instr M.raw.faults (envOfBound M.raw.bound) (request f Γ).val s t ↔
      M.raw.faults f .unit s t := by
  constructor
  · intro run
    cases run with
    | case_arg head =>
      cases head with
      | op_arg arg => cases arg
      | op_fault arg reply => cases arg; exact reply
    | case_inl _ branch | case_inr _ branch =>
      cases branch with | br value => cases value
  · exact fun fault => .case_arg (.op_fault .unit fault)

private theorem request_diverges (M : Shape.Model.{0,0,v,w} Instr Γ) (f : Instr) (s : M.raw.σ) :
    External.Diverges M.raw.instr M.raw.prim (.region (envOfBound M.raw.bound) (request f Γ).val s) ↔
      M.raw.prim f .unit s := by
  constructor
  · intro run
    cases run.unfold with
    | case_arg head =>
      cases head with
      | op_arg arg => cases arg
      | primitive arg active => cases arg; exact active
    | core step =>
      cases step with
      | case_inl _ branch | case_inr _ branch =>
        cases branch.unfold with
        | br value => cases value
        | core step => cases step
  · exact fun div => .fold (.case_arg (.primitive .unit div))

theorem request_denote (M : Shape.Model.{0,0,v,w} Instr Γ) (f : Instr) (s : M.raw.σ) :
    Shape.denote (.native (request f Γ)) M s =
      WithTop.some {o | match o with
        | .ret i a t => a = .unit ∧ M.raw.instr f .unit s (bitValue i) t
        | .fault t => M.raw.faults f .unit s t
        | .diverge => M.raw.prim f .unit s} := by
  apply congrArg WithTop.some
  ext o
  rw [mem_nativeOutcomes_iff _ (envOfBound_agrees M.raw.bound)]
  cases o with
  | ret i a t => exact request_ret M f s t i a
  | fault t => exact request_fault M f s t
  | diverge => exact request_diverges M f s

theorem exit_denote (e : Exit) (M : Institution.Observational.Model.{0,v,w} Instr Γ.length)
    (s : M.σ) : denote (e.region (Γ := Γ)) M s = e.behaviour s := by
  cases e with
  | ub => rfl
  | ret i =>
    apply congrArg WithTop.some
    ext o
    rw [mem_nativeOutcomes_iff _ (envOfBound_agrees M.bound), Set.mem_singleton_iff]
    cases o with
    | ret j a t =>
      have classify {label : Nat} (run : Region.Eval M.instr (envOfBound M.bound)
          (.br i.val .unit) s label a t) : label = i.val ∧ a = .unit ∧ t = s := by
        cases run with | br term => cases term; exact ⟨rfl, rfl, rfl⟩
      constructor
      · intro run
        obtain ⟨label, arg, final⟩ := classify run
        exact (Outcome.ret.injEq ..).mpr ⟨Fin.ext label, arg, final⟩
      · intro same
        obtain ⟨rfl, rfl, rfl⟩ := Outcome.ret.inj same
        exact .br .unit
    | fault t =>
      constructor
      · intro run
        cases run with | br value => cases value
      · intro eq
        cases eq
    | diverge =>
      constructor
      · intro run
        cases run.unfold with
        | br value => cases value
        | core step => cases step
      · intro eq
        cases eq

theorem exit_order {α : Type v} {σ : Type w} (p q : Exit) (s : σ) :
    (p.behaviour s : Behaviour Exits.length α σ) ≤ q.behaviour s ↔ p.Refines q := by
  cases p <;> cases q <;> simp [Exit.Refines, Exit.behaviour, WithTop.coe_le_coe]

theorem shaped_sound (p q : Endpoint) (h : NormalRefines p q) (M : Shape.Model.{0,0,v,w} Instr [])
    (s : M.raw.σ) : Shape.denote p.region M s ≤ Shape.denote q.region M s := by
  rcases h with ⟨key, rows⟩
  change (denote (.native (request p.first [])) M.raw s).bind
    (fun i a t => denote ((p.next i).region (Γ := [Exits.get i])) (extendModel M.raw a) t) ≤
    (denote (.native (request q.first [])) M.raw s).bind
    (fun i a t => denote ((q.next i).region (Γ := [Exits.get i])) (extendModel M.raw a) t)
  rw [key]
  refine Behaviour.bind_mono le_rfl fun i a t => ?_
  obtain ⟨key, exits⟩ := rows i
  change (denote (.native (request (p.next i).key [Exits.get i])) (extendModel M.raw a) t).bind
    (fun j b u => denote (((p.next i).exit j).region (Γ := [Exits.get j, Exits.get i]))
      (extendModel (extendModel M.raw a) b) u) ≤
    (denote (.native (request (q.next i).key [Exits.get i])) (extendModel M.raw a) t).bind
    (fun j b u => denote (((q.next i).exit j).region (Γ := [Exits.get j, Exits.get i]))
      (extendModel (extendModel M.raw a) b) u)
  rw [key]
  refine Behaviour.bind_mono le_rfl fun j b u => ?_
  rw [exit_denote, exit_denote]
  exact (exit_order _ _ _).mpr (exits j)

private theorem request_ordinary (M : Shape.Model.{0,0,v,w} Instr Γ) (f : Instr)
    (s t : M.raw.σ) (i : Tag) (a : Value M.raw.α) :
    (Shape.denote (.native (request f Γ)) M s).Ordinary (.ret i a t) ↔
      a = .unit ∧ M.raw.instr f .unit s (bitValue i) t := by
  rw [request_denote]
  exact ⟨And.right, fun hit => ⟨WithTop.coe_ne_top, hit⟩⟩

private theorem request_not_top (M : Shape.Model.{0,0,v,w} Instr Γ) (f : Instr) (s : M.raw.σ) :
    Shape.denote (.native (request f Γ)) M s ≠ ⊤ := by
  rw [request_denote]
  exact WithTop.coe_ne_top

private theorem row_top (r : Row) (M : Shape.Model.{0,0,v,w} Instr Γ) (s : M.raw.σ) :
    Shape.denote r.region M s = ⊤ ↔
      ∃ j t, M.raw.instr r.key .unit s (bitValue j) t ∧ r.exit j = .ub := by
  change (Shape.denote (.native (request r.key Γ)) M s).bind
    (fun j a t => denote ((r.exit j).region (Γ := Exits.get j :: Γ)) (extendModel M.raw a) t) = ⊤ ↔ _
  rw [bind_top_iff, or_iff_right (request_not_top M r.key s)]
  constructor
  · rintro ⟨j, a, t, hit, top⟩
    have step := ((request_ordinary M r.key s t j a).mp hit).2
    rw [exit_denote] at top
    refine ⟨j, t, step, ?_⟩
    cases selected : r.exit j with
    | ret i => simp [selected, Exit.behaviour] at top
    | ub => rfl
  · rintro ⟨j, t, step, ub⟩
    refine ⟨j, .unit, t, (request_ordinary M r.key s t j .unit).mpr ⟨rfl, step⟩, ?_⟩
    rw [ub]
    rfl

theorem endpoint_top (p : Endpoint) (M : Shape.Model.{0,0,v,w} Instr []) (s : M.raw.σ) :
    Shape.denote p.region M s = ⊤ ↔
      ∃ i t j u, M.raw.instr p.first .unit s (bitValue i) t ∧
        M.raw.instr (p.next i).key .unit t (bitValue j) u ∧ (p.next i).exit j = .ub := by
  change (Shape.denote (.native (request p.first [])) M s).bind
    (fun i a t => denote ((p.next i).region (Γ := [Exits.get i])) (extendModel M.raw a) t) = ⊤ ↔ _
  rw [bind_top_iff, or_iff_right (request_not_top M p.first s)]
  constructor
  · rintro ⟨i, a, t, hit, top⟩
    obtain ⟨rfl, first⟩ := (request_ordinary M p.first s t i a).mp hit
    have typed : Shape.ValueTyped M.atomType Value.unit (Exits.get i) := exit_type i ▸ .unit
    obtain ⟨j, u, second, ub⟩ := (row_top (p.next i) (M.extend typed) t).mp top
    exact ⟨i, t, j, u, first, second, ub⟩
  · rintro ⟨i, t, j, u, first, second, ub⟩
    have typed : Shape.ValueTyped M.atomType Value.unit (Exits.get i) := exit_type i ▸ .unit
    exact ⟨i, .unit, t, (request_ordinary M p.first s t i .unit).mpr ⟨rfl, first⟩,
      (row_top (p.next i) (M.extend typed) t).mpr ⟨j, u, second, ub⟩⟩

private theorem bitPayload_val (i : Tag) : (bitPayload i).val = bitValue i := by
  by_cases h : i = 0 <;> simp [bitPayload, bitValue, h]

private theorem bitValue_injective : Function.Injective (bitValue (α := Unit)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | cases h

private def actionBehaviour {n : Nat} (act : Action n) : Behaviour Exits.length Unit (Fin n) :=
  match act with
  | .reply i t => WithTop.some {Outcome.ret i .unit t}
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}

private theorem request_finite {n : Nat} (h : Handler n) (env : Syntax.Bindings Γ)
    (f : Instr) (s : Fin n) :
    Shape.denote (.native (request f Γ)) (Syntax.model h.primitives env) s =
      actionBehaviour (h f s) := by
  rw [request_denote]
  cases reply : h f s <;> apply congrArg WithTop.some <;> ext o <;> cases o <;>
    simp [Syntax.rawModel, Handler.primitives, Action.toReply, Syntax.StateReply.returns,
      reply, bitPayload_val, bitValue_injective.eq_iff, Outcome.ret.injEq, eq_comm, and_comm, and_left_comm, and_assoc, show Shape.ValueTyped Syntax.atomType
        (Value.unit : Value Unit) (instrSrc f) from .unit]
  · exact ⟨Syntax.StateReply.fault.inj, congrArg Syntax.Reply.fault⟩
  · rfl

theorem request_bind_finite {n : Nat} (h : Handler n) (env : Syntax.Bindings Γ)
    (f : Instr) (s : Fin n) (k : (i : Tag) → LambdaSSA.UB.Overlay.Region Instr (Exits.get i :: Γ) Exits) :
    Shape.denote (.lsubst (.native (request f Γ)) k) (Syntax.model h.primitives env) s =
      match h f s with
      | .reply i t => Shape.denote (k i)
          (Syntax.model h.primitives (env.push ⟨.unit, exit_type i ▸ .unit⟩)) t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} := by
  let M := Syntax.model h.primitives env
  let next (i : Tag) a t := denote (k i) (extendModel M.raw a) t
  change (Shape.denote (.native (request f Γ)) M s).bind next = _
  rw [request_finite]
  cases h f s with
  | reply i t =>
    change Behaviour.bind (WithTop.some {Outcome.ret i (Value.unit : Value Unit) t}) next = _
    rw [return_bind]
    exact denote_push h.primitives env ⟨.unit, exit_type i ▸ .unit⟩ (k i) t
  | fault t => exact fault_bind t next
  | diverge => exact diverge_bind next

private theorem row_finite {n : Nat} (r : Row) (h : Handler n) (env : Syntax.Bindings Γ)
    (s : Fin n) :
    Shape.denote r.region (Syntax.model h.primitives env) s = resultBehaviour (r.execute h s) := by
  unfold Row.region Row.execute
  rw [request_bind_finite]
  cases h r.key s with
  | reply i t =>
    change denote ((r.exit i).region (Γ := Exits.get i :: Γ))
      (Syntax.model h.primitives (env.push ⟨.unit, exit_type i ▸ .unit⟩)).raw t =
      resultBehaviour ((r.exit i).result t)
    rw [exit_denote]
    cases r.exit i <;> rfl
  | fault | diverge => rfl

theorem finite_observe {n : Nat} (p : Endpoint) (h : Handler n) (s : Fin n) :
    Shape.denote p.region h.model s = resultBehaviour (p.execute h s) := by
  unfold Endpoint.region Endpoint.execute
  rw [request_bind_finite]
  cases h p.first s with
  | reply i t => exact row_finite (p.next i) h _ t
  | fault | diverge => rfl

theorem result_order {n : Nat} (p q : Result 2 n) :
    resultBehaviour p ≤ resultBehaviour q ↔ p.refines q := by
  cases p <;> cases q <;> simp [resultBehaviour, Result.refines, WithTop.coe_le_coe]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest
