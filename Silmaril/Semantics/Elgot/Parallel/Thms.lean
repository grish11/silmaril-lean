module

public import Silmaril.Semantics.Elgot.Parallel.Defs
import Silmaril.Proofs.Semantics.Elgot.Parallel.Laws

/-! # Consequences of parallel pairing with the pure unit -/

public section

namespace Silmaril.Elgot.ParallelPairing

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
variable (P : ParallelPairing m) {A B : Type u}

/-- Symmetry supplies the other unitor. -/
theorem leftUnit (y : m B) :
    (Prod.snd <$> P.pair (pure (PUnit.unit : PUnit.{u + 1})) y) = y :=
  Proofs.leftUnit P y

/-- A pure right branch attaches its result to the left computation. -/
theorem pair_pure_right (x : m A) (b : B) :
    P.pair x (pure b) = ((fun a => (a, b)) <$> x) :=
  Proofs.pair_pure_right P x b

/-- A pure left branch attaches its result to the right computation. -/
theorem pair_pure_left (a : A) (y : m B) :
    P.pair (pure a) y = ((fun b => (a, b)) <$> y) :=
  Proofs.pair_pure_left P a y

/-- In particular the monad unit preserves pairing. -/
theorem pure_pair (a : A) (b : B) : P.pair (pure a) (pure b) = pure (a, b) := by
  rw [P.pair_pure_right, map_pure]

end Silmaril.Elgot.ParallelPairing
