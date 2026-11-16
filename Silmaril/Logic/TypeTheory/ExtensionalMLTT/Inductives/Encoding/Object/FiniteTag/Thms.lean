module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.ObjectFiniteTag

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

theorem cutoff_typing (count : ℕ) {Γ : Ctx} {t : Tm 0}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) (ht : Γ.JEqB 1 ∅ .nats t t) :
    Γ.JEqB 1 ∅ .nats (cutoff count t) (cutoff count t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag.cutoff_typing count hΓ ht

theorem cutoff_compute (count n : ℕ) {Γ : Ctx}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    Γ.JEqB 1 ∅ .nats (cutoff count (UnitVector.numeral n)) (UnitVector.numeral (code count n)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag.cutoff_compute count n hΓ

theorem code_eq_zero_iff (count n : ℕ) : code count n = 0 ↔ n < count :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag.code_eq_zero_iff count n

theorem formation (count : ℕ) {Γ : Ctx} (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    Γ.JEqB 1 ∅ (.univ 0) (Tag count) (Tag count) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag.formation count hΓ

theorem canonical_typing {count : ℕ} (i : Fin count) {Γ : Ctx}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    Γ.JEqB 1 ∅ (Tag count) (canonical i) (canonical i) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag.canonical_typing i hΓ

theorem canonical_denoteIn {count k : ℕ} (i : Fin count) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (β : Fin k → ZFSet.{u}) :
    (canonical i : Tm k).denoteIn U ρ β =
      SetSem.pair (Silmaril.Logic.SetTheory.numeral i.val) ∅ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag.canonical_denoteIn i U ρ β

/-- Every interpreted inhabitant comes from exactly the supplied finite range. -/
theorem mem_denoteIn_iff (count : ℕ) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (p : ZFSet.{u}) :
    p ∈ (Tag count : Tm 0).denoteIn U ρ Fin.elim0 ↔
      ∃ i : Fin count, p = SetSem.pair (Silmaril.Logic.SetTheory.numeral i.val) ∅ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag.mem_denoteIn_iff count U ρ p

noncomputable def semanticEquiv (count : ℕ) (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) :
    Fin count ≃ ((Tag count : Tm 0).denoteIn U ρ Fin.elim0) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag.semanticEquiv count U ρ

/-- The concrete two-family tags have independently checked closed derivations. -/
theorem first_of_two : Ctx.JEqB 1 ∅ .nil (Tag 2) (canonical (0 : Fin 2)) (canonical (0 : Fin 2)) :=
  canonical_typing 0 .nil_ok

theorem second_of_two : Ctx.JEqB 1 ∅ .nil (Tag 2) (canonical (1 : Fin 2)) (canonical (1 : Fin 2)) :=
  canonical_typing 1 .nil_ok

/-- The two concrete tags denote different values in every interpretation. -/
theorem two_tags_distinct (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) :
    (canonical (0 : Fin 2) : Tm 0).denoteIn U ρ Fin.elim0 ≠
      (canonical (1 : Fin 2) : Tm 0).denoteIn U ρ Fin.elim0 := by
  rw [canonical_denoteIn, canonical_denoteIn]
  intro h
  have hn := Silmaril.Logic.SetTheory.numeral_injective (ZFSet.pair_inj.1 h).1
  exact Nat.zero_ne_one hn

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag
