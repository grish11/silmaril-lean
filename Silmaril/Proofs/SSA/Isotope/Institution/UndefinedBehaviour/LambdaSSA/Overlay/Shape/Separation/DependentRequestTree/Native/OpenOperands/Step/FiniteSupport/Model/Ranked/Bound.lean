module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Ranked.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature Prefix)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty}

private theorem expand_follows_rank (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (fuel : Nat) (i : Fin R.length) (ranked : (g.ranks.get i).isSome = true)
    (bound : (g.ranks.get i).getD 0 < fuel) (incoming : Syntax.Payload (R.get i))
    {n : Nat} {probe : Prefix S.replies n}
    (path : (g.expand caller fuel i ranked bound incoming).Follows probe) :
    n ≤ (g.ranks.get i).getD 0 := by
  induction fuel generalizing i n with
  | zero => exact (Nat.not_lt_zero _ bound).elim
  | succ fuel ih =>
    rw [Table.expand] at path
    split at path
    · cases path
      exact Nat.zero_le _
    · rename_i f arg route typed row
      cases path with
      | stop => exact Nat.zero_le _
      | @step n f' arg' arms j value rest tail =>
        have edge : route j ∈ g.targets i := by
          rw [Table.targets, row, Row.targets]
          exact List.mem_ofFn.mpr ⟨j, rfl⟩
        have successor := Rank.ranked_successor g.targets ranked edge
        have smaller := successor.2.trans_le (Nat.le_of_lt_succ bound)
        have length := ih (route j) successor.1 smaller
          (cast (congrArg Syntax.Payload (typed j).symm) value) tail
        exact (Nat.succ_le_succ length).trans (Nat.succ_le_of_lt successor.2)

theorem extract_follows_rank (g : Table S R) (ok : g.entryCheck = true)
    (caller : Syntax.Payload (R.get g.entry)) {n : Nat} {probe : Prefix S.replies n}
    (path : (g.extract ok caller).Follows probe) : n ≤ (g.ranks.get g.entry).getD 0 :=
  expand_follows_rank g caller _ g.entry _ _ caller path

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked
