module

public import Silmaril.Semantics.Elgot.Partition.Defs
import Silmaril.Proofs.Semantics.Elgot.Iteration.Partition

/-! # Equations for partitioned complete iteration -/

public section

namespace Silmaril.Elgot

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {A B : Type u}

/-- Grouping recursive transitions into the inner and outer iterators
preserves the complete run, with no progress or termination hypothesis. -/
theorem iter_partition (body : A → m (B ⊕ A)) (inner : A → Bool) :
    iter (iter (partitionStep body inner)) = iter body := by
  rw [LawfulElgotMonad.codiagonal, Proofs.Semantics.Elgot.flatten_partition]

/-- At an outer state, one inner run performs just the original body. -/
theorem iter_partition_outer (body : A → m (B ⊕ A)) (inner : A → Bool)
    (state : A) (outer : inner state = false) :
    iter (partitionStep body inner) state = body state := by
  rw [congrFun (LawfulElgotMonad.fixpoint (partitionStep body inner)) state]
  simp only [partitionStep, outer, Bool.false_eq_true, ite_false, bind_map_left, Sum.elim_inl, bind_pure]

/-- The destination-based cut preserves the complete run. A feedback
edge to an outer state resumes the outer iterator, even from an inner state. -/
theorem iter_partition_target (body : A → m (B ⊕ A)) (inner : A → Bool) :
    iter (iter (partitionStepByTarget body inner)) = iter body := by
  rw [LawfulElgotMonad.codiagonal, Proofs.Semantics.Elgot.flatten_partition_target]

end Silmaril.Elgot
