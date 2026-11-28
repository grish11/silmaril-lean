module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.BranchNormalization.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch

/-! # Strictness of raw-to-guarded branch normalization -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch

open Silmaril.Isotope.LambdaSSA
open Silmaril.Elgot.ITree
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (region)
open Paper.WithProjectionReturnsAndUnitEta (Step)
open Paper.WithProjectionReturnsAndUnitEta.BranchNormalization (toRaw normalize rawClass)

/-- The old joined syntax distinguishes the raw visible operation from its bound form.
Every existing equation respects the observation after erasing head primitives in branch position. -/
theorem rawBranch_separation :
    ¬ Paper.Extension.Eqv Step [] rawBranch rawBranch.bindBranchArguments [(Ty.unit : Ty Empty)] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch.rawBranch_separation

open Paper.WithBoundEntryEta.Generators (Candidate)

/-- The proposed join still separates a raw visible branch from its bound form,
even with exact typing in both entry-let generators. -/
theorem candidate_branch_separation :
    ¬ Paper.Extension.Eqv Candidate [] rawBranch rawBranch.bindBranchArguments [(Ty.unit : Ty Empty)] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch.candidate_branch_separation

/-- The once-bound η generator already fails in the proposed join at arity
zero, where eliminating the CFG on both sides exposes branch binding. -/
theorem candidate_zero_arity_ne :
    let bs : Fin 0 → Region Op := Fin.elim0
    ¬ Paper.Extension.Eqv Candidate [] (.cfg rawBranch 0 bs)
      (rawBranch.bindBranchArguments.lsubst (cfgEntryContinuations bs)) [(Ty.unit : Ty Empty)] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch.candidate_zero_arity_ne

/-- Guarded inclusion after normalization changes this raw quotient class. -/
theorem reverse_roundTrip_fails :
    toRaw (normalize (rawClass rawBranch_typed)) ≠ rawClass rawBranch_typed :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch.reverse_roundTrip_fails

/-- Ordinary weak-tree evaluation issues the same single visible call on both forms. -/
theorem one_request :
    region visiblePrim (fun _ => .unit) rawBranch =
        vis .request (fun _ => pure (0, .unit)) ∧
      region visiblePrim (fun _ => .unit) rawBranch.bindBranchArguments =
        vis .request (fun _ => pure (0, .unit)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch.one_request

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch
