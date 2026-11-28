module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Steps
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Scan.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Mathlib.Data.Fintype.Pigeonhole

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction hiding Row Table
open OpenOperands (ConfigurationEnumeration blockPoint)
open OpenOperands.Silent
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open Relation (TransGen)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {σ : Type v}

theorem resolve_none_iff (g : Table S R) (fuel : Nat) (i : Fin R.length) :
    g.resolve fuel i = none ↔ search (g.labelRows) fuel i = none := by
  induction fuel generalizing i with
  | zero => simp [OpenOperands.Silent.Table.resolve, search]
  | succ fuel ih =>
    cases row : g.row i with
    | guarded _ => simp [OpenOperands.Silent.Table.resolve, search, Table.labelRows, row]
    | jump j _ => simp [OpenOperands.Silent.Table.resolve, search, Table.labelRows, row, ih]

private theorem silent_replay (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (p : Packet R) (s : σ) (exhausted : g.resolve R.length p.1 = none) :
    ∃ path : Nat → Packet R, path 0 = p ∧
      ∀ n, Branch (g.feedback caller prim) (blockPoint (path n) s) (blockPoint (path (n + 1)) s) := by
  obtain ⟨orbit, entry, steps⟩ := scan_exhausted_path (g.labelRows) p.1 ((resolve_none_iff g _ _).mp exhausted)
  let At (n : Nat) := { q : Packet R // q.1 = orbit n }
  have advance (n : Nat) (x : At n) :
      ∃ next : At (n + 1), Branch (g.feedback caller prim) (blockPoint x.val s) (blockPoint next.val s) := by
    obtain ⟨⟨i, incoming⟩, position⟩ := x
    change i = orbit n at position
    subst i
    have rowStep := steps n
    cases row : g.row (orbit n) with
    | guarded code => simp [Table.labelRows, row] at rowStep
    | jump j arg =>
      have nextEq : j = orbit (n + 1) := by simpa [Table.labelRows, row] using rowStep
      exact ⟨⟨⟨j, arg.eval ((g.visible.bindings caller).push incoming)⟩, nextEq⟩,
        jump_branch g caller prim row incoming s⟩
  let orbitTyped : (n : Nat) → At n :=
    Nat.rec ⟨p, entry.symm⟩ (fun n incoming => (advance n incoming).choose)
  exact ⟨fun n => (orbitTyped n).val, rfl, fun n => (advance n (orbitTyped n)).choose_spec⟩

private theorem silent_revisits (configs : ConfigurationEnumeration R) (path : Nat → Packet R) :
    ∃ i j : Nat, i < j ∧ path i = path j := by
  classical
  let code (p : Packet R) : Fin configs.configs.length :=
    ⟨configs.configs.idxOf p, List.idxOf_lt_length_of_mem (configs.complete p)⟩
  have injective : Function.Injective code := by
    intro a b same
    have decode (x : Packet R) : configs.configs.get (code x) = x := by
      exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (configs.complete x))
    exact (decode a).symm.trans ((congrArg configs.configs.get same).trans (decode b))
  obtain ⟨i, j, different, same⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (configs.configs.length + 1) => code (path i.val)) (by simp)
  rcases Nat.lt_or_gt_of_ne (fun eq => different (Fin.ext eq)) with before | after
  · exact ⟨i, j, before, injective same⟩
  · exact ⟨j, i, after, injective same.symm⟩

theorem exhausted_replay (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (configs : ConfigurationEnumeration R) (p : Packet R) (s : σ)
    (exhausted : g.resolve R.length p.1 = none) :
    ∃ path : Nat → Packet R, path 0 = p ∧
      (∀ n, Feedback.Step (g.feedback caller prim) (blockPoint (path n) s) (blockPoint (path (n + 1)) s)) ∧
      ∃ i j : Nat, i < j ∧ path i = path j := by
  obtain ⟨path, first, steps⟩ := silent_replay g caller prim p s exhausted
  refine ⟨path, first, fun n => ?_, silent_revisits configs path⟩
  obtain ⟨i, a, t, next, branch⟩ := steps n
  exact (step_of_branch_iff branch).mpr next

theorem exhausts_close (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (p : Packet R) (s : σ) (exhausted : g.resolve R.length p.1 = none) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) = WithTop.some {Outcome.diverge} := by
  obtain ⟨path, first, steps⟩ := silent_replay g caller prim p s exhausted
  rw [← first]
  exact close_along_infinite (fun n => blockPoint (path n) s) (fun n => .single (steps n))

theorem exhausts_observes [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) (checked : g.checkNative raw = true)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (s : σ)
    (exhausted : g.resolve R.length g.entry = none) :
    Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings caller)) s =
      WithTop.some {Outcome.diverge} := by
  have same : raw = g.native := Subtype.ext (CFG.Dependent.Native.sameRegion_eq checked)
  subst raw
  change (denote (.native g.native) (model prim (g.visible.bindings caller)).raw s).bind _ = _
  rw [native_close g caller prim s, exhausts_close g caller prim ⟨g.entry, caller⟩ s exhausted]
  exact Syntax.diverge_bind _

theorem head_correct [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (caller : Payload (R.get g.entry)) (p : Packet R) (prim : StatePrimitives Φ σ) (s : σ)
    {result : HeadResult S R} (found : g.head? raw caller p = some result) :
    raw = g.native ∧
      match result with
      | .ready head =>
        ∃ q, Feedback.Reaches (g.feedback caller prim) (blockPoint p s) q ∧
          g.feedback caller prim q = (head.execute prim s).routed ∧
          Feedback.close (g.feedback caller prim) (blockPoint p s) = Feedback.close (g.feedback caller prim) q
      | .diverge =>
        Feedback.close (g.feedback caller prim) (blockPoint p s) = WithTop.some {Outcome.diverge} := by
  unfold OpenOperands.Silent.Table.head? at found
  split at found
  · rename_i checked
    refine ⟨Subtype.ext (CFG.Dependent.Native.sameRegion_eq checked), ?_⟩
    obtain ⟨i, packet⟩ := p
    cases resolved : g.resolve R.length i with
    | none =>
      have eq : HeadResult.diverge = result := Option.some.inj (by simpa only [resolved] using found)
      subst result
      exact exhausts_close g caller prim ⟨i, packet⟩ s resolved
    | some row =>
      have eq : HeadResult.ready (evalHead g.selected ((g.visible.bindings caller).push packet) row) = result :=
        Option.some.inj (by simpa only [resolved] using found)
      subst result
      obtain ⟨q, path, step⟩ := resolve_segment g caller prim R.length i resolved packet s
      refine ⟨q, ?_, step, close_along path⟩
      clear step
      induction path with
      | refl => exact .refl
      | tail _ branch ih =>
        obtain ⟨j, value, t, next, run⟩ := branch
        exact .tail ih ((step_of_branch_iff run).mpr next)
  · cases found

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent
