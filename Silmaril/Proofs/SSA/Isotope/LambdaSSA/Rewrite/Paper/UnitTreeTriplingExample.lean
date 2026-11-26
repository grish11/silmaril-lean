module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.UnitTree.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingExample

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory.ComponentTripling.UnitTree.Example
open Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Elgot.ITree

local notation "E" => Event Op Empty

theorem body_typed : ValueBranches [State] body [Ty.coprod Exit State] :=
  .case (.var rfl)
    (.let₁ (.op (.var rfl))
      (.case (.var rfl)
        (.br rfl (.inr (.inr (.inl (.var rfl)))))
        (.br rfl (.inl (.inl .unit)))))
    (.case (.var rfl)
      (.let₁ (.op (.var rfl))
        (.case (.var rfl)
          (.br rfl (.inr (.inr (.inr (.var rfl)))))
          (.br rfl (.inl (.inr (.pair .unit .unit))))))
      (.br rfl (.inr (.inl (.var rfl)))))

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

private theorem ordered_syntax :
    orderedBody = .case (.var 0)
      (.let₁ (.op .first (.var 0))
        (.case (.var 0)
          (port (.inr (.inr (.inl (.var 0)))))
          (port (.inl (.inl .unit)))))
      (.case (.var 0)
        (.let₁ (.op .second (.var 0))
          (.case (.var 0)
            (port (.inr (.inr (.inr (.var 0)))))
            (port (.inl (.inr (.pair .unit .unit))))))
        (port (.inr (.inl (.var 0))))) := rfl

theorem first_request :
    region (F := E) request (fun _ => .inl .unit) orderedBody =
      vis (.call .first .unit) (fun
        | .inl x => ret (2, .inr (.inl x))
        | .inr _ => ret (0, .unit)
        | _ => diverge) := by
  rw [ordered_syntax]
  simp only [port, region, term, request, pure_bind, vis_bind, extend]
  congr 1
  funext v
  cases v <;> rfl

theorem second_request :
    region (F := E) request (fun _ => .inr (.inl .unit)) orderedBody =
      vis (.call .second .unit) (fun
        | .inl x => ret (2, .inr (.inr x))
        | .inr _ => ret (1, .pair .unit .unit)
        | _ => diverge) := by
  rw [ordered_syntax]
  simp only [port, region, term, request, pure_bind, vis_bind, extend]
  congr 1
  funext v
  cases v <;> rfl

theorem last_returns :
    region (F := E) request (fun _ => .inr (.inr .unit)) orderedBody =
      ret (2, .inl .unit) := by
  rw [ordered_syntax]
  simp only [port, region, term, pure_bind, extend]
  rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingExample
