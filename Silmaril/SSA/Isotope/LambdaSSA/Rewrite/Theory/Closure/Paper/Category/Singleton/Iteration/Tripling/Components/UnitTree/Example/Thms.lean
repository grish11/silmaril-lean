module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.UnitTree.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.UnitTree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingExample

/-! # Exact feedback checks for the written three-tag round -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.UnitTree.Example

open CategoryTheory CategoryTheory.Limits
open Semantics.Interaction Silmaril.Elgot.ITree
open Paper.Extension.Singleton (iterateChosen)
open Paper.Extension.Singleton.ThreeCycle (triple triple_step_unit_tree)

abbrev UnitSeed := Paper.WithUnitEta.Step (τ := Ty Empty) (Φ := Op)
abbrev FoldSeed := Paper.WithCaseReturns.BinaryFold.JoinedStep (τ := Ty Empty) (Φ := Op) false

theorem body_typed : ValueBranches [State] body [Ty.coprod Exit State] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingExample.body_typed

/-- The very same written region at the chosen ordered output boundary. -/
noncomputable def round (Seed : VCtx (Ty Empty) → Region Op → Region Op → LCtx (Ty Empty) → Prop) :
    Paper.Extension.Singleton.ofType Seed State ⟶
      Paper.Extension.Singleton.ofType Seed Exit ⨿ Paper.Extension.Singleton.ofType Seed State :=
  Paper.Extension.Singleton.ofRegion Seed body_typed ≫
    (Paper.Extension.Singleton.sumIso Seed Exit State).hom

/-- The two outward ports remain ordered before the recurrence port. -/
theorem ordered_typed : ValueBranches [State] orderedBody [U, Ty.product U U, State] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingExample.ordered_typed

/-- The first visible call can cross to the middle tag or exit at port zero. -/
theorem first_request :
    region (F := Event Op Empty) request (fun _ => .inl .unit) orderedBody =
      vis (.call .first .unit) (fun
        | .inl x => ret (2, .inr (.inl x))
        | .inr _ => ret (0, .unit)
        | _ => diverge) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingExample.first_request

/-- The second visible call can cross to the last tag or exit at port one. -/
theorem second_request :
    region (F := Event Op Empty) request (fun _ => .inr (.inl .unit)) orderedBody =
      vis (.call .second .unit) (fun
        | .inl x => ret (2, .inr (.inr x))
        | .inr _ => ret (1, .pair .unit .unit)
        | _ => diverge) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingExample.second_request

/-- The last tag closes the three-tag cycle. -/
theorem last_returns :
    region (F := Event Op Empty) request (fun _ => .inr (.inr .unit)) orderedBody =
      ret (2, .inl .unit) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingExample.last_returns

/-- The normalized and batched proof returns to the literal written round
in the existing Unit-η quotient. -/
theorem withUnit_triples :
    iterateChosen UnitSeed (triple (round UnitSeed)) = iterateChosen UnitSeed (round UnitSeed) :=
  triple_step_unit_tree UnitSeed (fun h => h) shape (round UnitSeed)

/-- The same exact boundary and ordered exits in the BinaryFold quotient. -/
theorem binaryFold_triples :
    iterateChosen FoldSeed (triple (round FoldSeed)) = iterateChosen FoldSeed (round FoldSeed) :=
  triple_step_unit_tree FoldSeed (fun h => .inl (Paper.WithCaseReturns.includeUnit false h))
    shape (round FoldSeed)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.UnitTree.Example
