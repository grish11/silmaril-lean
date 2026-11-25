module

public import Silmaril.Semantics.Calco2019.Maybe.Hyperextensive.Iteration.Defs
public import Silmaril.Semantics.Calco2019.Thms
import Silmaril.Proofs.Semantics.Calco2019.Maybe.Hyperextensive.Iteration
import Silmaril.Proofs.Semantics.Calco2019.Maybe.Hyperextensive.Codiagonal

/-! # Initiality of Maybe on hyperextensive categories, CALCO 2019 §1.3 -/

public section

universe u v

namespace Silmaril.Calco2019.Maybe

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Hyperextensive C] {P : Coproducts C}
  {E : C} (terminal : IsTerminal E)

/-- The deterministic solution is uniquely characterized by unfolding and by giving
failure on every invariant pure subcomputation. -/
theorem solve_isCanonical {X Y : C} (f : X ⟶ P.sum (P.sum Y E) X) :
    Canonical terminal f (solve terminal f) :=
  Proofs.solve_canonical terminal f

theorem solve_eq_of_canonical {X Y : C} {f : X ⟶ P.sum (P.sum Y E) X}
    {s : X ⟶ P.sum Y E} (hs : Canonical terminal f s) : s = solve terminal f :=
  Proofs.solve_unique terminal f hs

/-- The loop equations of Maybe with every Kleisli body admissible. -/
@[expose]
noncomputable def hyperextensiveFixpoints :
    (Guardedness.greatest (P.kleisli (monad P E))).Fixpoints where
  iterate f _ := kleisliArrow (loop terminal f.of)
  fixpoint f _ := by exact Proofs.kleisli_fixpoint terminal f

/-- Naturality follows by transforming the return branch. Codiagonal follows
by comparing the least pre-fixed solutions in the partial-result order. -/
theorem hyperextensive_naturalCodiagonal :
    (hyperextensiveFixpoints (P := P) terminal).NaturalCodiagonal where
  naturality f k _ _ := Proofs.kleisli_natural terminal f k
  codiagonal f _ _ _ _ := Proofs.kleisli_codiagonal terminal f

/-- A pure state change preserves finite exits and invariant recurrence. -/
theorem hyperextensive_uniformity :
    (hyperextensiveFixpoints (P := P) terminal).Uniform (Kleisli.Adjunction.toKleisli (monad P E)) :=
  fun f g h _ _ square => Proofs.kleisli_uniform terminal f g h square

/-- The Maybe monad with total Elgot iteration on a hyperextensive category. -/
@[expose]
noncomputable def hyperextensiveElgot : GuardedElgotMonad P where
  monad := monad P E
  guard := Guardedness.greatest _
  iteration :=
    { toFixpoints := hyperextensiveFixpoints terminal
      naturalCodiagonal := hyperextensive_naturalCodiagonal terminal
      dinaturality := (hyperextensiveFixpoints terminal).dinaturality_of_uniform
        (P.kleisliPreservesSelected _) (fun X => ⟨X.of, rfl⟩)
        (hyperextensive_naturalCodiagonal terminal) (hyperextensive_uniformity terminal) }
  uniformity := hyperextensive_uniformity terminal

theorem hyperextensiveElgot_total : (hyperextensiveElgot (P := P) terminal).IsElgot :=
  fun _ => trivial

/-- For a terminal object, (X \mapsto X + 1) is initial among total Elgot monads. -/
noncomputable def hyperextensiveInitial :
    IsInitial (⟨hyperextensiveElgot terminal, hyperextensiveElgot_total terminal⟩ : TotalElgot P) :=
  initialOfHyperextensive terminal (hyperextensiveElgot terminal) (hyperextensiveElgot_total terminal)
    rfl

end Silmaril.Calco2019.Maybe
