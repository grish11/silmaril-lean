module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Steps
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Scan.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Mathlib.Data.Fintype.Pigeonhole

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Table Row
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (ConfigurationEnumeration Head StateTransition blockPoint)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
open CFG.Dependent (Packet)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open Syntax (Payload StatePrimitives)
open Relation (ReflTransGen)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R : List Syntax.Ty} {σ : Type v}

theorem scan_ready (g : Table S R) (caller : Payload (R.get g.entry)) (fuel : Nat)
    (p : Packet R) {head : Head S R} (resolved : g.scan caller fuel p = some head) :
    ∃ q, ReflTransGen (fun a b => g.step caller a = .inl b) p q ∧ g.step caller q = .inr head := by
  induction fuel generalizing p with
  | zero => cases resolved
  | succ fuel ih =>
    rw [Table.scan] at resolved
    cases next : g.step caller p with
    | inl q =>
      rw [next] at resolved
      obtain ⟨r, path, ready⟩ := ih q resolved
      exact ⟨r, .head next path, ready⟩
    | inr exposed =>
      rw [next] at resolved
      cases resolved
      exact ⟨p, .refl, next⟩

private def code (configs : ConfigurationEnumeration R) (p : Packet R) : Fin configs.configs.length :=
  ⟨configs.configs.idxOf p, List.idxOf_lt_length_of_mem (configs.complete p)⟩

private theorem decode_code (configs : ConfigurationEnumeration R) (p : Packet R) :
    configs.configs.get (code configs p) = p :=
  List.getElem_idxOf _

private def codedRows (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (i : Fin configs.configs.length) :
    Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Row configs.configs.length configs.configs.length 1 :=
  match g.step caller (configs.configs.get i) with
  | .inl q => .repeat (code configs q)
  | .inr _ => .stop (.ret i 0)

private theorem scan_none_iff (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (fuel : Nat) (p : Packet R) :
    g.scan caller fuel p = none ↔ search (codedRows g configs caller) fuel (code configs p) = none := by
  induction fuel generalizing p with
  | zero => simp [Table.scan, search]
  | succ fuel ih =>
    rw [Table.scan, search, codedRows, decode_code]
    cases g.step caller p with
    | inl q => exact ih q
    | inr head => simp

theorem exhausted_replay (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (p : Packet R)
    (exhausted : g.scan caller configs.configs.length p = none) :
    ∃ path : Nat → Packet R, path 0 = p ∧
      (∀ n, g.step caller (path n) = .inl (path (n + 1))) ∧
      ∃ i j : Nat, i < j ∧ j ≤ configs.configs.length ∧ path i = path j := by
  obtain ⟨orbit, first, steps⟩ := scan_exhausted_path (codedRows g configs caller) (code configs p)
    ((scan_none_iff g configs caller _ _).mp exhausted)
  let path (n : Nat) := configs.configs.get (orbit n)
  refine ⟨path, (congrArg configs.configs.get first).trans (decode_code configs p), fun n => ?_, ?_⟩
  · have edge := steps n
    unfold codedRows at edge
    change g.step caller (path n) = .inl (path (n + 1))
    cases h : g.step caller (path n) with
    | inl q =>
      change (match g.step caller (path n) with | .inl q => _ | .inr _ => _) = _ at edge
      rw [h] at edge
      have eq := Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Row.repeat.inj edge
      exact congrArg Sum.inl ((decode_code configs q).symm.trans (congrArg configs.configs.get eq))
    | inr head =>
      change (match g.step caller (path n) with | .inl q => _ | .inr _ => _) = _ at edge
      rw [h] at edge
      cases edge
  · obtain ⟨i, j, different, same⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (configs.configs.length + 1) => orbit i.val) (by simp)
    rcases Nat.lt_or_gt_of_ne (fun eq => different (Fin.ext eq)) with before | after
    · exact ⟨i, j, before, Nat.le_of_lt_succ j.isLt, congrArg configs.configs.get same⟩
    · exact ⟨j, i, after, Nat.le_of_lt_succ i.isLt, congrArg configs.configs.get same.symm⟩

theorem close_silent (g : Table S R) (caller : Payload (R.get g.entry))
    (prim : StatePrimitives Φ σ) (s : σ) {p q : Packet R}
    (path : ReflTransGen (fun a b => g.step caller a = .inl b) p q) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) =
      Feedback.close (g.feedback caller prim) (blockPoint q s) := by
  induction path with
  | refl => rfl
  | tail _ edge ih =>
    exact ih.trans (close_branch ((feedback_step g caller prim _ s).trans (by rw [edge]; rfl)))

theorem exhausts_close (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ)
    (exhausted : g.scan caller configs.configs.length p = none) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) = WithTop.some {Outcome.diverge} := by
  obtain ⟨path, first, steps, _⟩ := exhausted_replay g configs caller p exhausted
  rw [← first]
  exact close_infinite_of_singleton (fun n => blockPoint (path n) s) fun n =>
    ⟨(path (n + 1)).1, (path (n + 1)).2.val, s, rfl,
      (feedback_step g caller prim _ s).trans (by rw [steps n]; rfl)⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
