module

public import Silmaril.Semantics.Brookes.Iteration.Defs
public import Silmaril.Semantics.Brookes.Parallel.Thms
public import Silmaril.Semantics.Elgot.Parallel.Defs

/-! # Closed Brookes shuffle as a parallel pairing -/

@[expose] public section

namespace Silmaril.Semantics.Brookes.Behavior

universe u v

variable {Store : Type u} {A B : Type v}

/-- The monad's pure map changes only the terminal result of a trace. -/
theorem map_eq_mapResult (f : A → B) (p : Behavior Store A) :
    f <$> p = p.mapResult f :=
  (mapResult_eq_bind f p).symm

/-- Closed shuffle on a shared store supplies the symmetric pairing for ordinary
value maps. -/
def parallelPairing (Store : Type u) : Elgot.ParallelPairing (Behavior.{u, v} Store) where
  pair := parallel
  natural f g p q := by
    simpa only [map_eq_mapResult] using parallel_natural f g p q
  swap p q := by
    simpa only [map_eq_mapResult] using parallel_symm p q
  assoc p q r := by
    simpa only [map_eq_mapResult] using parallel_assoc p q r
  rightUnit p := by
    change Prod.fst <$> p.parallel (ret (PUnit.unit : PUnit.{v + 1})) = p
    rw [map_eq_mapResult, parallel_ret_right, mapResult_comp, mapResult_eq_bind]
    exact bind_ret p

end Silmaril.Semantics.Brookes.Behavior
