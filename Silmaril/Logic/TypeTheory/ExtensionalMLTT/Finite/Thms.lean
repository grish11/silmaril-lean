module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Finite

@[expose] public section

/-! # Finite MLTT semantics and model existence

Only levels mentioned in a bounded judgment affect its interpretation. Towers
at heights one, two and three supply concrete models in successively larger
Lean carriers. This module supplies model existence; `Finite.Soundness`
proves actual bounded-derivation soundness and closed Empty consistency
using these finite supplies.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

/-- The generic interpretation agrees with the original hierarchy semantics. -/
theorem ETm.denoteIn_eq_denote (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (t : ETm k) :
    t.denoteIn T.U ρ β = t.denote T ρ β :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.denoteIn_eq_denote T ρ β t

theorem ECtx.satIn_iff_sat (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) (Γ : ECtx) :
    Γ.SatIn T.U ρ ↔ Γ.Sat T ρ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.satIn_iff_sat T ρ Γ

theorem EJdg.validIn_iff_valid (T : SetHierarchy.{u}) (j : EJdg) :
    j.ValidIn T.U ↔ j.Valid T :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.validIn_iff_valid T j

/-- A bounded term's value depends only on in-range universe levels. -/
theorem ETm.denoteIn_congr {U V : ℕ → ZFSet.{u}} (ρ : String → ZFSet.{u})
    {n k : ℕ} (β : Fin k → ZFSet.{u}) (t : ETm k) (ht : t.UsesBelow n)
    (hUV : ∀ i < n, U i = V i) : t.denoteIn U ρ β = t.denoteIn V ρ β :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.denoteIn_congr ρ β t ht hUV

/-- A bounded context's satisfaction depends only on in-range levels. -/
theorem ECtx.satIn_congr {U V : ℕ → ZFSet.{u}} (ρ : String → ZFSet.{u})
    {n : ℕ} (Γ : ECtx) (hΓ : Γ.UsesBelow n) (hUV : ∀ i < n, U i = V i) :
    Γ.SatIn U ρ ↔ Γ.SatIn V ρ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.satIn_congr ρ Γ hΓ hUV

/-- Arbitrary out-of-range entries in a finite lookup cannot affect validity. -/
theorem EJdg.validIn_congr {U V : ℕ → ZFSet.{u}} {n : ℕ}
    (j : EJdg) (hj : j.UsesBelow n) (hUV : ∀ i < n, U i = V i) :
    j.ValidIn U ↔ j.ValidIn V :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.validIn_congr j hj hUV

namespace Finite

/-- A finite tower supplies a model of the corresponding MLTT institution. -/
theorem model_nonempty (n : ℕ) [Silmaril.Logic.SetTheory.HasFiniteTower.{u} n] :
    Nonempty (room.{u} n).Mod :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.model_nonempty n

/-- One object-language universe has a concrete model in the next Lean carrier. -/
theorem model_one : Nonempty (room.{u + 1} 1).Mod := model_nonempty 1

/-- Two object-language universes have a model two Lean carriers higher. -/
theorem model_two : Nonempty (room.{u + 2} 2).Mod := model_nonempty 2

/-- Three object-language universes have a model three Lean carriers higher. -/
theorem model_three : Nonempty (room.{u + 3} 3).Mod := model_nonempty 3

end Finite

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
