module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Defs
import Mathlib.Data.Set.Image

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.State

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.InterpreterScript
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (resultBehaviour)

universe u v w

variable {labels : Nat} {α : Type u} {σ : Type v} {τ : Type w}

private theorem outcome_injective (e : σ ↪ τ) :
    Function.Injective (Outcome.mapState (labels := labels) (α := α) e) := by
  intro a b same
  cases a <;> cases b <;> simp [Outcome.mapState, e.injective.eq_iff] at same ⊢
  all_goals exact same

theorem mapState_le_iff (e : σ ↪ τ) (a b : Behaviour labels α σ) :
    a.mapState e ≤ b.mapState e ↔ a ≤ b := by
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;>
    simp [Behaviour.mapState, Set.image_subset_image_iff (outcome_injective e)]

theorem resultBehaviour_mapState {n m : Nat} (e : Fin n → Fin m) (outcome : Result 2 n) :
    resultBehaviour (outcome.mapState e) = (resultBehaviour outcome).mapState e := by
  cases outcome <;> simp [resultBehaviour, Result.mapState, Behaviour.mapState, Outcome.mapState]

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {n m : Nat}

private theorem query_injective (e : Fin n ↪ Fin m) :
    Function.Injective (Query.mapState (Φ := Φ) e) := by
  intro a b same
  have key := congrArg Query.key same
  change (a.op, a.arg.val, e a.state) = (b.op, b.arg.val, e b.state) at key
  obtain ⟨op, rest⟩ := Prod.mk.inj key
  obtain ⟨arg, state⟩ := Prod.mk.inj rest
  exact Query.key_injective (Prod.ext op (Prod.ext arg (e.injective state)))

variable [DecidableEq Φ]

private theorem lookup_mapState (e : Fin n ↪ Fin m) (row : Row Φ n) (q : Query Φ n) :
    (row.mapState e).lookup (q.mapState e) = (row.lookup q).map (Syntax.Reply.mapState e) := by
  obtain ⟨key, answer⟩ := row
  by_cases same : key = q
  · subst q
    simp [Row.lookup, Row.mapState]; rfl
  · have different : key.mapState e ≠ q.mapState e := fun eq => same (query_injective e eq)
    simp [Row.lookup, Row.mapState, same, different]; rfl

private theorem script_lookup_mapState (e : Fin n ↪ Fin m) (script : List (Row Φ n)) (q : Query Φ n) :
    (script.map (Row.mapState e)).findSome? (Row.lookup (q.mapState e)) =
      (script.findSome? (Row.lookup q)).map (Syntax.Reply.mapState e) := by
  induction script with
  | nil => rfl
  | cons row tail ih =>
    simp only [List.map_cons, List.findSome?_cons, lookup_mapState, ih]
    cases row.lookup q <;> rfl

theorem interpret_mapState (e : Fin n ↪ Fin m) (script : List (Row Φ n))
    (f : Φ) (a : Syntax.Payload (instrSrc f)) (s : Fin n) :
    interpret (script.map (Row.mapState e)) f a (e s) = (interpret script f a s).mapState e := by
  let q : Query Φ n := ⟨f, a, s⟩
  change ((script.map (Row.mapState e)).findSome? (Row.lookup (q.mapState e))).getD .diverge =
    ((script.findSome? (Row.lookup q)).getD .diverge).mapState e
  rw [script_lookup_mapState]
  cases script.findSome? (Row.lookup q) <;> rfl

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.State
