module

public import Silmaril.Semantics.Calco2019.Maybe.Types.Defs
import Silmaril.Proofs.Semantics.Calco2019.Maybe.Types

/-! # Initiality of Maybe on Set, CALCO 2019 §1.3 -/

public section

universe u

namespace Silmaril.Calco2019.Maybe.Types

open CategoryTheory CategoryTheory.Limits

instance : LawfulMonad Model.{u} := Proofs.lawful
instance : Elgot.LawfulElgotMonad Model.{u} := Proofs.lawfulElgot

/-- The library's finite-successful-run iteration on the carrier (X + 1). -/
@[expose]
noncomputable def elgot : GuardedElgotMonad (typeCoproducts : Coproducts (Type u)) :=
  ofLawfulMonad Model

theorem elgot_total : elgot.{u}.IsElgot := ofLawfulMonad_isElgot Model

theorem elgot_monad : elgot.{u}.monad = monad typeCoproducts PUnit.{u + 1} :=
  Proofs.monad_eq

/-- A pure loop in Set partitions into its exact finite exit times and its invariant residual. -/
theorem decompose {X Y : Type u} (f : X ⟶ typeCoproducts.sum Y X) :
    Nonempty (LoopDecomposition f) :=
  Proofs.decompose f

/-- The Maybe monad on Set is initial among total Elgot monads. -/
noncomputable def initial : IsInitial (⟨elgot.{u}, elgot_total⟩ : TotalElgot typeCoproducts) :=
  initialOfDecomposition CategoryTheory.Limits.Types.isTerminalPUnit.{u} elgot.{u} elgot_total
    elgot_monad fun f => decompose f

end Silmaril.Calco2019.Maybe.Types
