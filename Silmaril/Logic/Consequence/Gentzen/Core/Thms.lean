module

public import Silmaril.Logic.Consequence.Gentzen.Thms
public import Silmaril.Logic.Consequence.Multi.Defs

/-!
# Gentzen sequents over the core multiple-conclusion systems

A thin bridge to `Silmaril.Logic.Consequence.Multi` and `…Signed`:

* `seq_eq_multiSystem`: `Seq C` is `MultiSystem C C` (`rfl`).
* `weakSubset_iff_weak`: the default (`⊆`, both sides) weakening is core's `MultiSystem.Weak`.
  So closures under `defaultRules` are `Weak` (`derives_weak`).
* `valid_eq_multiEntails`: `Valid sat` is core's `multiEntails sat sat`. Hence `roomMulti` is
  closed under the default Gentzen rules (`roomMulti_closed`), and a sound relation's closure
  is sound for it.
* `entails_eq_valid_single`: single conclusions, `Refutation.Entails sat = (Valid sat).single`.
* `viaUnsat_neg_iff`: with an `InvolutiveNeg`, the UNSAT conversion is
  `check (Γ ++ negateEach Δ)`. Involution gives no satisfaction law; for signed atoms under a
  valuation (`signedSat`), the laws hold: `signedSat_negSound`, `signedSat_negComplete`.
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen

universe u v w

variable {C : Type u}

theorem seq_eq_multiSystem : Seq C = MultiSystem C C := rfl

theorem weakSubset_iff_weak {S : Seq C} : WeakSubset S ↔ MultiSystem.Weak S :=
  ⟨fun h => ⟨fun _ _ hΓ _ hd => h hΓ (fun _ hx => hx) hd, fun _ _ _ hΔ hd =>
      h (fun _ hx => hx) hΔ hd⟩,
    fun ⟨hl, hr⟩ _ _ _ _ hΓ hΔ hd => hr hΔ (hl hΓ hd)⟩

theorem derives_weak (S : Seq C) : MultiSystem.Weak (Derives defaultRules S) :=
  weakSubset_iff_weak.1 (derives_closed defaultRules S).weak

variable {M : Type v}

theorem valid_eq_multiEntails (sat : M → C → Prop) : Valid sat = multiEntails sat sat := rfl

theorem multiEntails_closed (sat : M → C → Prop) : Closed defaultRules (multiEntails sat sat) :=
  valid_closed

theorem roomMulti_closed (R : Logic.Institution.Room.{w, u, v}) : Closed defaultRules (roomMulti R) :=
  valid_closed

theorem entails_eq_valid_single (sat : M → C → Prop) :
    Refutation.Entails sat = MultiSystem.single (Valid sat) := by
  funext Γ c; exact propext entails_iff_valid

theorem viaUnsat_neg_iff [InvolutiveNeg C] {check : List C → Prop} {Γ Δ : List C} :
    viaUnsat check (-·) Γ Δ ↔ check (Γ ++ negateEach Δ) := Iff.rfl

/-- Signed atoms under a valuation of the atoms. -/
def signedSat {A : Type u} (τ : M → A → Prop) (m : M) : Signed A → Prop
  | .pos a => τ m a
  | .neg a => ¬ τ m a

theorem signedSat_negSound {A : Type u} (τ : M → A → Prop) :
    NegSound (signedSat τ) (-·) := by
  rintro m (a | a) h h'
  · exact (h : ¬ τ m a) h'
  · exact h' (h : τ m a)

theorem signedSat_negComplete {A : Type u} (τ : M → A → Prop) :
    NegComplete (signedSat τ) (-·) := by
  rintro m (a | a) h
  · exact (h : ¬ τ m a)
  · exact (not_not.1 h : τ m a)

end Silmaril.Consequence.Gentzen
