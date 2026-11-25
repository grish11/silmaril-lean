module

public import Silmaril.Semantics.Calco2019.Examples.Probability.Thms

/-! # Countably supported subdistributions and finite iteration -/

@[expose] public section

open scoped ENNReal Classical

universe u

namespace Silmaril.Calco2019.Examples.Probability

/-- A weight function of total mass at most one. Finite total mass implies countable support. -/
structure Subdist (X : Type u) where
  weight : X → ℝ≥0∞
  mass_le_one : (∑' x, weight x) ≤ 1

namespace Subdist

variable {X Y : Type u}

instance : CoeFun (Subdist X) (fun _ => X → ℝ≥0∞) := ⟨weight⟩

@[ext] theorem ext {p q : Subdist X} (h : ∀ x, p x = q x) : p = q := by
  cases p; cases q
  congr
  exact funext h

/-- A point mass. -/
noncomputable def point (x : X) : Subdist X :=
  ⟨fun y => if y = x then 1 else 0, by rw [tsum_ite_eq]⟩

/-- Kleisli substitution sums over the possible intermediate results. -/
noncomputable def mix (p : Subdist X) (k : X → Subdist Y) : Subdist Y :=
  ⟨fun y => ∑' x, p x * k x y, by
    rw [tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    calc
      _ ≤ ∑' x, p x * 1 := tsum_le_tsum fun x => mul_le_mul_right (k x).mass_le_one _
      _ ≤ 1 := by simpa only [mul_one] using p.mass_le_one⟩

noncomputable instance : Monad Subdist where
  pure := point
  bind := mix

theorem pure_apply (x y : X) : (pure x : Subdist X) y = if y = x then 1 else 0 := rfl

theorem bind_apply (p : Subdist X) (k : X → Subdist Y) (y : Y) :
    (p >>= k) y = ∑' x, p x * k x y := rfl

/-- The always-diverging subdistribution. -/
def bottom : Subdist X := ⟨fun _ => 0, by simp⟩

@[simp] theorem bottom_apply (x : X) : (bottom : Subdist X) x = 0 := rfl

/-- A full distribution embeds by retaining each weight. -/
def ofPMF (p : PMF X) : Subdist X :=
  ⟨p, p.tsum_coe.le⟩

@[simp] theorem ofPMF_apply (p : PMF X) (x : X) : ofPMF p x = p x := rfl

/-- The order of subdistributions compares the weights pointwise. -/
instance : LE (Subdist X) := ⟨fun p q => ∀ x, p x ≤ q x⟩

instance : PartialOrder (Subdist X) where
  le_refl _ _ := le_rfl
  le_trans _ _ _ hp hq x := (hp x).trans (hq x)
  le_antisymm _ _ hp hq := ext fun x => le_antisymm (hp x) (hq x)

/-- The pointwise supremum of an increasing sequence still has mass at most one. -/
noncomputable def limit (p : ℕ → Subdist X) (hp : Monotone p) : Subdist X :=
  ⟨fun x => ⨆ n, p n x, by
    rw [tsum_iSup_nat (fun n x => p n x) (fun _ _ h x => hp h x)]
    exact iSup_le fun n => (p n).mass_le_one⟩

theorem limit_apply (p : ℕ → Subdist X) (hp : Monotone p) (x : X) :
    limit p hp x = ⨆ n, p n x := rfl

/-- One unfolding of a subdistribution loop. -/
noncomputable def unfoldLoop (f : X → Subdist (Y ⊕ X)) (g : X → Subdist Y) : X → Subdist Y :=
  f >=> Sum.elim pure g

/-- Finite approximants discard mass still in the recursive summand. -/
noncomputable def unfoldFor (f : X → Subdist (Y ⊕ X)) : ℕ → X → Subdist Y
  | 0 => fun _ => bottom
  | n + 1 => unfoldLoop f (unfoldFor f n)

end Subdist
end Silmaril.Calco2019.Examples.Probability
