module

public import Silmaril.Semantics.Elgot.Defs

/-! # Parallel pairing on an Elgot carrier -/

@[expose] public section

namespace Silmaril.Elgot

universe u v

/-- A symmetric lax monoidal pairing for the cartesian products of ordinary
types. The unit is the monad's pure unit. Naturality uses ordinary functions.
The structure is independent of Kleisli sequencing and of the iteration operator. -/
structure ParallelPairing (m : Type u → Type v) [Monad m] where
  /-- Run both branches and retain both results in branch order. -/
  pair {A B : Type u} : m A → m B → m (A × B)
  natural {A B C D : Type u} (f : A → C) (g : B → D) (x : m A) (y : m B) :
    (Prod.map f g <$> pair x y) = pair (f <$> x) (g <$> y)
  swap {A B : Type u} (x : m A) (y : m B) :
    (Prod.swap <$> pair x y) = pair y x
  assoc {A B C : Type u} (x : m A) (y : m B) (z : m C) :
    ((fun p : (A × B) × C => (p.1.1, p.1.2, p.2)) <$> pair (pair x y) z) =
      pair x (pair y z)
  rightUnit {A : Type u} (x : m A) :
    (Prod.fst <$> pair x (pure (PUnit.unit : PUnit.{u + 1}))) = x

end Silmaril.Elgot
