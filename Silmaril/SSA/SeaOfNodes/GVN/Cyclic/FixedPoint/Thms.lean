module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint

open Diamond (Signature ValueSort)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data} {n : Nat}
variable {inputs : List (ValueSort Data)} {sorts : Fin n → ValueSort Data}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- The number of represented classes is bounded by the number of vertices. -/
theorem classCount_le_vertices (p : Partition n) : classCount p ≤ n :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.classCount_le p

/-- A split with no merges strictly increases the number of classes. -/
theorem classCount_lt_of_split {fine coarse : Partition n} (h : Refines fine coarse)
    {i j : Fin n} (same : coarse i = coarse j) (different : fine i ≠ fine j) :
    classCount coarse < classCount fine :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.classCount_lt_of_split h same different

/-- Each round preserves existing class separations. -/
theorem refine_no_merges (g : Graph Op inputs sorts) (p : Partition n) : Refines (refine g p) p :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.refine_refines g p

/-- Every unstable round strictly increases the number of represented classes. -/
theorem classCount_lt_refine (g : Graph Op inputs sorts) (p : Partition n) (h : ¬ Stable g p) :
    classCount p < classCount (refine g p) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.refine_count_lt g p h

/-- Even a run with insufficient fuel preserves existing separations. -/
theorem run_no_merges (g : Graph Op inputs sorts) (fuel : Nat) (p : Partition n) :
    Refines (run g fuel p) p :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.run_refines g fuel p

/-- One round per possible additional class suffices to reach stability. -/
theorem run_stable_of_fuel (g : Graph Op inputs sorts) (fuel : Nat) (p : Partition n)
    (enough : n - classCount p ≤ fuel) : Stable g (run g fuel p) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.run_stable g fuel p enough

/-- The default budget reaches a stable refinement of the typed seed. -/
theorem normalize_stable (g : Graph Op inputs sorts) :
    Stable g (normalize g) ∧ Refines (normalize g) (seed g) :=
  ⟨run_stable_of_fuel g n (seed g) (Nat.sub_le ..), run_no_merges g n (seed g)⟩

/-- An extra round preserves exactly the same-class relation of the result. -/
theorem normalize_fixed (g : Graph Op inputs sorts) (i j : Fin n) :
    refine g (normalize g) i = refine g (normalize g) j ↔ normalize g i = normalize g j :=
  (stable_iff_refine_eq g _).mp (normalize_stable g).1 i j

/-- Every stable refinement of the seed refines the result. Together with
`normalize_stable`, this characterizes the coarsest stable refinement up
to its same-class relation. -/
theorem normalize_coarsest (g : Graph Op inputs sorts) (p : Partition n)
    (stable : Stable g p) (h : Refines p (seed g)) : Refines p (normalize g) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.stable_refines_run g stable n (seed g) h

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint
