module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingExample

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory.ComponentTripling.StructuralExample
open Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Elgot.ITree

theorem body_typed : ValueBranches [State] body [Ty.coprod Exit State] :=
  .let₁ (.op (.var rfl)) (.case (.var rfl)
    (.br rfl (.inr (.var rfl))) (.br rfl (.inl (.var rfl))))

theorem ordered_typed : ValueBranches [State] orderedBody [U, Ty.product U U, State] := by
  apply body_typed.lsubst
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .case (.var rfl)
      (.case (.var rfl) (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 1) rfl (.var rfl)))
      (.br (ℓ := 2) rfl (.var rfl))
  | succ i => simp [At] at hi

private def port (a : Tm Op) : Region Op :=
  .case a (.case (.var 0) (.br 0 (.var 0)) (.br 1 (.var 0))) (.br 2 (.var 0))

theorem pair_request (first second : Value Empty) :
    region (F := Event Op Empty) request (fun _ => .pair first second) orderedBody =
      vis (.call .sample (.pair first second)) (fun
        | .inl state => ret (2, state)
        | .inr (.inl x) => ret (0, x)
        | .inr (.inr y) => ret (1, y)
        | _ => diverge) := by
  change region (F := Event Op Empty) request (fun _ => .pair first second)
    (.let₁ (.op .sample (.var 0))
      (.case (.var 0) (port (.inr (.var 0))) (port (.inl (.var 0))))) = _
  simp only [port, region, term, request, pure_bind, vis_bind, extend]
  congr 1
  funext value
  cases value with
  | inr x => cases x <;> rfl
  | _ => rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingExample
