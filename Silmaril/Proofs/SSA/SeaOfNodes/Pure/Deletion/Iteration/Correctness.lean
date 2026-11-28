module

public import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Iteration.Defs
import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Pass.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.Deletion.Iteration

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure.Deletion (delete? delete?_outputs_eq)
open Silmaril.SSA.SeaOfNodes.Pure.Deletion.Iteration
open Diamond (Model Signature Ty Val)
open Silmaril.SSA.RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data} {args ports : List (Ty Data)}
variable {start final : Table Op args ports} {positions : List Nat}

theorem first_none (table : Table Op args ports) : first? table = none ↔ NoEligible table := by
  constructor
  · intro miss sort candidate
    have check := List.findSome?_eq_none_iff.mp miss ⟨sort, candidate⟩ (GVN.Pass.mem_candidates candidate)
    exact Option.attach_eq_none_iff.mp (Option.map_eq_none_iff.mp check)
  · intro miss
    apply List.findSome?_eq_none_iff.mpr
    intro candidate _
    exact Option.map_eq_none_iff.mpr (Option.attach_eq_none_iff.mpr (miss candidate.2))

theorem count (trace : Trace start final positions) :
    final.sigs.length + positions.length = start.sigs.length := by
  induction trace with
  | done => simp
  | step edit _ _ ih =>
    have size : edit.next.sigs.length + 1 = _ := edit.deleted.erasure.shorter
    simp only [List.length_cons]
    omega

theorem stopped (trace : Trace start final positions) : NoEligible final := by
  induction trace with
  | done table miss => exact (first_none table).mp miss
  | step _ _ _ ih => exact ih

theorem packet_eq (trace : Trace start final positions) (m : Model.{u, v, w} Op)
    (input : Tuple (Val m.value) args) : final.eval m input = start.eval m input := by
  induction trace with
  | done => rfl
  | step edit _ _ ih => exact ih.trans (delete?_outputs_eq edit.accepted m input PUnit.unit)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.Deletion.Iteration
