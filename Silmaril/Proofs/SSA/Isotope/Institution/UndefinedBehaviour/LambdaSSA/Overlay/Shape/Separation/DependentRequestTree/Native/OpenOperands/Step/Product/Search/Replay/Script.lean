module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.InterpreterScript

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.InterpreterScript

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {states : Nat}

private theorem read_transport (prim : Syntax.Primitives Φ states) {q r : Query Φ states} (eq : q = r) :
    (eq ▸ q.read prim : Syntax.Reply (instrTrg r.op) states) = r.read prim := by
  cases eq
  rfl

theorem consistent_of_realizes {prim : Syntax.Primitives Φ states} {rows : List (Row Φ states)}
    (run : Realizes prim rows) : Consistent rows := by
  intro a ha b hb same
  rw [← run a ha, ← run b hb]
  exact read_transport prim same

theorem extend_realizes [DecidableEq Φ] {rows : List (Row Φ states)} (ok : Consistent rows)
    (fallback : Syntax.Primitives Φ states) : Realizes (extend rows fallback) rows := by
  intro row mem
  change (rows.findSome? (Row.lookup row.1)).getD (row.1.read fallback) = row.2
  cases found : rows.findSome? (Row.lookup row.1) with
  | none =>
    have missing := (List.findSome?_eq_none_iff.mp found) row mem
    simp [Row.lookup] at missing
  | some answer =>
    obtain ⟨origin, listed, hit⟩ := List.exists_of_findSome?_eq_some found
    unfold Row.lookup at hit
    split at hit
    · rename_i same
      exact (Option.some.inj hit).symm.trans (ok origin listed row mem same)
    · cases hit

theorem feasible_iff [DecidableEq Φ] (rows : List (Row Φ states)) :
    (∃ prim : Syntax.Primitives Φ states, Realizes prim rows) ↔ Consistent rows :=
  ⟨fun ⟨_, run⟩ => consistent_of_realizes run,
    fun ok => ⟨extend rows (fun _ _ _ => .diverge), extend_realizes ok _⟩⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.InterpreterScript
