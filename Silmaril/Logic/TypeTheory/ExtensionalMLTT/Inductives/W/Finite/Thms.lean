module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite

@[expose] public section

/-! # Finite MLTT semantics and model existence

Only levels mentioned in a bounded judgment affect its interpretation. Towers
at heights one, two and three supply concrete models in successively larger
Lean carriers. The bounded inference calculus and its consistency results are
available separately in `Finite.Derivation`.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

universe u

/-- The generic interpretation agrees with the original hierarchy semantics. -/
theorem Tm.denoteIn_eq_denote (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (t : Tm k) :
    t.denoteIn T.U ρ β = t.denote T ρ β :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.denoteIn_eq_denote T ρ β t

theorem Ctx.satIn_iff_sat (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) (Γ : Ctx) :
    Γ.SatIn T.U ρ ↔ Γ.Sat T ρ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.satIn_iff_sat T ρ Γ

theorem Jdg.validIn_iff_valid (T : SetHierarchy.{u}) (j : Jdg) :
    j.ValidIn T.U ↔ j.Valid T :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.validIn_iff_valid T j

/-- A bounded term's value depends only on in-range universe levels. -/
theorem Tm.denoteIn_congr {U V : ℕ → ZFSet.{u}} (ρ : String → ZFSet.{u})
    {n k : ℕ} (β : Fin k → ZFSet.{u}) (t : Tm k) (ht : t.UsesBelow n)
    (hUV : ∀ i < n, U i = V i) : t.denoteIn U ρ β = t.denoteIn V ρ β :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.denoteIn_congr ρ β t ht hUV

/-- A bounded context's satisfaction depends only on in-range levels. -/
theorem Ctx.satIn_congr {U V : ℕ → ZFSet.{u}} (ρ : String → ZFSet.{u})
    {n : ℕ} (Γ : Ctx) (hΓ : Γ.UsesBelow n) (hUV : ∀ i < n, U i = V i) :
    Γ.SatIn U ρ ↔ Γ.SatIn V ρ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.satIn_congr ρ Γ hΓ hUV

/-- Arbitrary out-of-range entries in a finite lookup cannot affect validity. -/
theorem Jdg.validIn_congr {U V : ℕ → ZFSet.{u}} {n : ℕ}
    (j : Jdg) (hj : j.UsesBelow n) (hUV : ∀ i < n, U i = V i) :
    j.ValidIn U ↔ j.ValidIn V :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.validIn_congr j hj hUV

namespace Finite

/-- A finite tower supplies a model of the corresponding MLTT institution. -/
theorem model_nonempty (n : ℕ) [Silmaril.Logic.SetTheory.HasFiniteTower.{u} n] :
    Nonempty (room.{u} n).Mod :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.model_nonempty n

/-- One object-language universe has a concrete model in the next Lean carrier. -/
theorem model_one : Nonempty (room.{u + 1} 1).Mod := model_nonempty 1

/-- Two object-language universes have a model two Lean carriers higher. -/
theorem model_two : Nonempty (room.{u + 2} 2).Mod := model_nonempty 2

/-- Three object-language universes have a model three Lean carriers higher. -/
theorem model_three : Nonempty (room.{u + 3} 3).Mod := model_nonempty 3

end Finite

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
