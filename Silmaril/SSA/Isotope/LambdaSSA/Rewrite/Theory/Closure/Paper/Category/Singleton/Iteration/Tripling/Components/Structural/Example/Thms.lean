module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingExample

/-! # Exact tripling and ordered exits for the written product round -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.StructuralExample

open CategoryTheory CategoryTheory.Limits
open Semantics.Interaction Silmaril.Elgot.ITree
open Paper.Extension.Singleton (iterateChosen)
open Paper.Extension.Singleton.ThreeCycle (triple triple_step_structural)

abbrev UnitSeed := Paper.WithUnitEta.Step (τ := Ty Empty) (Φ := Op)
abbrev FoldSeed := Paper.WithCaseReturns.BinaryFold.JoinedStep (τ := Ty Empty) (Φ := Op) false

theorem body_typed : ValueBranches [State] body [Ty.coprod Exit State] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingExample.body_typed

/-- The same written region at the original product state. -/
noncomputable def round (Seed : VCtx (Ty Empty) → Region Op → Region Op → LCtx (Ty Empty) → Prop) :
    Paper.Extension.Singleton.ofType Seed State ⟶
      Paper.Extension.Singleton.ofType Seed Exit ⨿ Paper.Extension.Singleton.ofType Seed State :=
  Paper.Extension.Singleton.ofRegion Seed body_typed ≫
    (Paper.Extension.Singleton.sumIso Seed Exit State).hom

theorem ordered_typed : ValueBranches [State] orderedBody [U, Ty.product U U, State] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingExample.ordered_typed

/-- The visible request retains each operand, and the reply routes to the
whole next pair or to the original outward ports. -/
theorem pair_request (first second : Value Empty) :
    region (F := Event Op Empty) request (fun _ => .pair first second) orderedBody =
      vis (.call .sample (.pair first second)) (fun
        | .inl state => ret (2, state)
        | .inr (.inl x) => ret (0, x)
        | .inr (.inr y) => ret (1, y)
        | _ => diverge) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingExample.pair_request first second

theorem withUnit_triples :
    iterateChosen UnitSeed (triple (round UnitSeed)) = iterateChosen UnitSeed (round UnitSeed) :=
  triple_step_structural UnitSeed (fun h => h) shape (round UnitSeed)

theorem binaryFold_triples :
    iterateChosen FoldSeed (triple (round FoldSeed)) = iterateChosen FoldSeed (round FoldSeed) :=
  triple_step_structural FoldSeed (fun h => .inl (Paper.WithCaseReturns.includeUnit false h))
    shape (round FoldSeed)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.StructuralExample
