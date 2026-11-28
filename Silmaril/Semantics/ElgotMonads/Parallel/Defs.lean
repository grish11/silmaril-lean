module

public import Silmaril.Semantics.ElgotMonads.Thms
public import Silmaril.Semantics.Elgot.Parallel.Defs

/-! # Tuple pairing for finite-success Elgot models -/

@[expose] public section

namespace Silmaril.Elgot.ParallelPairing

universe u v

/-- Form a tuple by sequencing the two computations in left-to-right order. -/
def bindPair {m : Type u → Type v} [Monad m] {A B : Type u} (x : m A) (y : m B) :
    m (A × B) :=
  x >>= fun a => y >>= fun b => pure (a, b)

/-- Sequencing defines a symmetric pairing when reversing branch evaluation
preserves the ordered tuple of results. -/
def ofBind {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (comm : ∀ {A B : Type u} (x : m A) (y : m B),
      bindPair x y = (y >>= fun b => x >>= fun a => pure (a, b))) : ParallelPairing m where
  pair := bindPair
  natural _ _ _ _ := by simp [bindPair, ← bind_pure_comp, bind_assoc]
  swap x y := by
    simpa [bindPair, ← bind_pure_comp, bind_assoc] using (comm y x).symm
  assoc _ _ _ := by simp [bindPair, ← bind_pure_comp, bind_assoc]
  rightUnit _ := by simp [bindPair, ← bind_pure_comp, bind_assoc]

/-- Lift a pairing pointwise through a shared, immutable environment. -/
def reader {m : Type u → Type v} [Monad m] {ρ : Type u} (P : ParallelPairing m) :
    ParallelPairing (ReaderT ρ m) where
  pair x y r := P.pair (x.run r) (y.run r)
  natural f g x y := funext fun r => P.natural f g (x.run r) (y.run r)
  swap x y := funext fun r => P.swap (x.run r) (y.run r)
  assoc x y z := funext fun r => P.assoc (x.run r) (y.run r) (z.run r)
  rightUnit x := funext fun r => P.rightUnit (x.run r)

end Silmaril.Elgot.ParallelPairing
