module

public import Silmaril.Semantics.Calco2019.Examples.Probability.Defs
import Mathlib.Tactic.NormNum

@[expose] public section

open scoped ENNReal BigOperators Classical

namespace Silmaril.Calco2019.Examples.Probability.Proofs


variable {X : Type*} {Y : Type*}

private theorem step_mono (f : X → PMF (Y ⊕ X)) :
    Monotone (step f) := by
  intro g h hg x y
  exact add_le_add_right (tsum_le_tsum fun z => mul_le_mul_right (hg z y) _) _

private theorem approx_mono (f : X → PMF (Y ⊕ X)) : Monotone (approx f) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact fun _ _ => zero_le
  | succ n ih => exact step_mono f ih

theorem tsum_iSup_nat {A : Type*} (g : ℕ → A → ℝ≥0∞) (hg : Monotone g) :
    (∑' a, ⨆ n, g n a) = ⨆ n, ∑' a, g n a := by
  classical
  have sum_comm (s : Finset A) : (∑ a ∈ s, ⨆ n, g n a) = ⨆ n, ∑ a ∈ s, g n a := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih]
      apply ENNReal.iSup_add_iSup_of_monotone
      · exact fun _ _ h => hg h a
      · exact fun _ _ h => Finset.sum_le_sum fun b _ => hg h b
  simp only [tsum_eq_iSup_sum, sum_comm]
  exact iSup_comm

theorem least_fixpoint (f : X → PMF (Y ⊕ X)) : step f (least f) = least f := by
  funext x y
  unfold step least
  simp_rw [ENNReal.mul_iSup]
  rw [tsum_iSup_nat (fun n z => f x (.inr z) * approx f n z y)
    (fun _ _ h z => mul_le_mul_right (approx_mono f h z y) _), ENNReal.add_iSup]
  change (⨆ n, approx f (n + 1) x y) = ⨆ n, approx f n x y
  exact Monotone.iSup_nat_add (fun _ _ h => approx_mono f h x y) 1

theorem least_le (f : X → PMF (Y ⊕ X)) {g : X → Y → ℝ≥0∞}
    (hg : step f g ≤ g) : least f ≤ g := by
  have h (n : ℕ) : approx f n ≤ g := by
    induction n with
    | zero => exact fun _ _ => zero_le
    | succ n ih => exact (step_mono f ih).trans hg
  exact fun x y => iSup_le fun n => h n x y

private theorem row_split (p : PMF (Y ⊕ X)) :
    (∑' y, p (.inl y)) + (∑' z, p (.inr z)) = 1 := by
  rw [← Summable.tsum_sum (f := fun w => p w) CompleteLattice.summable
    CompleteLattice.summable, p.tsum_coe]

private theorem mass_step (f : X → PMF (Y ⊕ X)) (g : X → Y → ℝ≥0∞) (x : X) :
    mass (step f g) x = (∑' y, f x (.inl y)) + ∑' z, f x (.inr z) * mass g z := by
  unfold mass step
  rw [tsum_add, tsum_comm (f := fun y z => f x (.inr z) * g z y)]
  simp_rw [ENNReal.tsum_mul_left]

theorem mass_le_one (f : X → PMF (Y ⊕ X)) (x : X) : mass (least f) x ≤ 1 := by
  have h (n : ℕ) (x : X) : mass (approx f n) x ≤ 1 := by
    induction n generalizing x with
    | zero => simp [mass, approx]
    | succ n ih =>
      rw [approx, mass_step, ← row_split (f x)]
      exact add_le_add_right (tsum_le_tsum fun z => by
        simpa using mul_le_mul_right (ih z) (f x (.inr z))) _
  unfold mass least
  rw [tsum_iSup_nat _ (fun _ _ h y => approx_mono f h x y)]
  exact iSup_le fun n => h n x

theorem mass_pos (f : X → PMF (Y ⊕ X)) (hf : Guarded f) (x : X) : 0 < mass (least f) x := by
  obtain ⟨y, hy⟩ := hf x
  have h : f x (.inl y) ≤ least f x y := by
    rw [← congrFun (congrFun (least_fixpoint f) x) y, step]
    exact le_self_add
  exact hy.trans_le (h.trans (le_tsum (f := least f x) y))

/-- Assign the missing subprobability to an explicit fallback distribution. -/
theorem completion (f : X → PMF (Y ⊕ X)) (fallback : PMF Y) :
    let g := fun x y => least f x y + (1 - mass (least f) x) * fallback y
    (∀ x, mass g x = 1) ∧ step f g = g := by
  let m := mass (least f)
  let d : X → ℝ≥0∞ := fun x => 1 - m x
  have split (x : X) : d x + m x = 1 := tsub_add_cancel_of_le (mass_le_one f x)
  have harmonic (x : X) : (∑' z, f x (.inr z) * d z) = d x := by
    have hm : (∑' y, f x (.inl y)) + (∑' z, f x (.inr z) * m z) = m x := by
      simpa only [least_fixpoint] using (mass_step f (least f) x).symm
    apply (ENNReal.add_left_inj (ne_top_of_le_ne_top ENNReal.one_ne_top (mass_le_one f x))).mp
    change _ + m x = d x + m x
    rw [split x]
    calc
      (∑' z, f x (.inr z) * d z) + m x =
          (∑' y, f x (.inl y)) + ((∑' z, f x (.inr z) * d z) + ∑' z, f x (.inr z) * m z) := by
        rw [← hm]
        ac_rfl
      _ = 1 := by
        rw [← tsum_add]
        simp_rw [← mul_add, split, mul_one]
        exact row_split (f x)
  refine ⟨fun x => ?_, ?_⟩
  · change (∑' y, (least f x y + d x * fallback y)) = 1
    rw [tsum_add, ENNReal.tsum_mul_left, fallback.tsum_coe, mul_one, add_comm]
    exact split x
  · funext x y
    have h := congrFun (congrFun (least_fixpoint f) x) y
    have hsum :
        (∑' z, f x (.inr z) * (least f z y + d z * fallback y)) =
          (∑' z, f x (.inr z) * least f z y) + (∑' z, f x (.inr z) * d z) * fallback y := by
      simp_rw [mul_add, ← mul_assoc]
      rw [tsum_add, ENNReal.tsum_mul_right]
    change f x (.inl y) + (∑' z, f x (.inr z) * (least f z y + d z * fallback y)) =
      least f x y + d x * fallback y
    rw [hsum, harmonic, ← add_assoc]
    exact congrArg (· + d x * fallback y) h

theorem chain_guarded (label : ℕ → Y) : Guarded (chain label) := by
  intro n
  refine ⟨label n, ?_⟩
  rw [chain_inl, ite_eq_left rfl, exit]
  apply ENNReal.div_pos
  · simp
  · exact survivalWeight_ne_top n

theorem chain_step (label : ℕ → Y) (g : ℕ → Y → ℝ≥0∞) (n : ℕ) (y : Y) :
    step (chain label) g n y =
      (if y = label n then exit n else 0) + advance n * g (n + 1) y := by
  classical
  rw [step, chain_inl]
  congr 1
  rw [tsum_eq_single (n + 1)]
  · simp
  · intro k hk
    simp [hk]

private theorem scaled_step (label : ℕ → Y) (g : ℕ → Y → ℝ≥0∞) (n : ℕ) (y : Y) :
    survivalWeight n * step (chain label) g n y =
      (if y = label n then (2⁻¹ : ℝ≥0∞) ^ (n + 1) else 0) + survivalWeight (n + 1) * g (n + 1) y := by
  classical
  rw [chain_step, mul_add, ← mul_assoc, advance,
    ENNReal.mul_div_cancel (survivalWeight_ne_zero n) (survivalWeight_ne_top n)]
  by_cases hy : y = label n
  · simp [hy, exit, ENNReal.mul_div_cancel (survivalWeight_ne_zero n) (survivalWeight_ne_top n)]
  · simp [hy]

private theorem scaled_approx (label : ℕ → Y) (k n : ℕ) (y : Y) :
    survivalWeight n * approx (chain label) k n y =
      ∑ i ∈ Finset.range k, if y = label (n + i) then (2⁻¹ : ℝ≥0∞) ^ (n + i + 1) else 0 := by
  classical
  induction k generalizing n with
  | zero => simp [approx]
  | succ k ih =>
    rw [approx, scaled_step, ih, Finset.sum_range_succ']
    have h : (∑ i ∈ Finset.range k,
        if y = label (n + (i + 1)) then (2⁻¹ : ℝ≥0∞) ^ (n + (i + 1) + 1) else 0) =
        ∑ i ∈ Finset.range k,
          if y = label (n + 1 + i) then (2⁻¹ : ℝ≥0∞) ^ (n + 1 + i + 1) else 0 := by
      congr 1
      funext i
      rw [show n + (i + 1) = n + 1 + i by omega]
    rw [h, add_comm]
    simp


theorem scaled_least (label : ℕ → Y) (n : ℕ) (y : Y) :
    survivalWeight n * least (chain label) n y =
      ∑' i : ℕ, if y = label (n + i) then (2⁻¹ : ℝ≥0∞) ^ (n + i + 1) else 0 := by
  classical
  unfold least
  rw [ENNReal.mul_iSup, ENNReal.tsum_eq_iSup_nat]
  simp_rw [scaled_approx]

theorem scaled_mass (label : ℕ → Y) (n : ℕ) :
    survivalWeight n * mass (least (chain label)) n = (2⁻¹ : ℝ≥0∞) ^ n := by
  classical
  unfold mass
  rw [← ENNReal.tsum_mul_left]
  simp_rw [scaled_least]
  rw [tsum_comm]
  simp only [tsum_ite_eq]
  calc
    (∑' i : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + i + 1)) =
        (2⁻¹ : ℝ≥0∞) ^ (n + 1) * ∑' i : ℕ, (2⁻¹ : ℝ≥0∞) ^ i := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro i
      rw [← pow_add, show n + i + 1 = n + 1 + i by omega]
    _ = (2⁻¹ : ℝ≥0∞) ^ n := by
      rw [ENNReal.tsum_geometric_two, pow_succ, mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by simp), mul_one]

private theorem two_mul_weight_zero : (2 : ℝ≥0∞) * survivalWeight 0 = 3 := by
  rw [survivalWeight, pow_zero, mul_add, mul_one,
    ENNReal.mul_inv_cancel (by norm_num) (by simp)]
  norm_num

theorem chain_mass_zero (label : ℕ → Y) : mass (least (chain label)) 0 = 2 / 3 := by
  apply (ENNReal.eq_div_iff (by norm_num) (by simp)).2
  rw [← two_mul_weight_zero, mul_assoc, scaled_mass, pow_zero, mul_one]

private theorem least_false_succ (n : ℕ) : least (chain coloredExit) (n + 1) false = 0 := by
  apply (ENNReal.mul_right_inj (survivalWeight_ne_zero (n + 1))
    (survivalWeight_ne_top (n + 1))).mp
  rw [mul_zero, scaled_least]
  simp [coloredExit]

private theorem least_false_zero : least (chain coloredExit) 0 false = exit 0 := by
  have h := congrFun (congrFun (least_fixpoint (chain coloredExit)) 0) false
  rw [chain_step, least_false_succ 0] at h
  simpa [coloredExit] using h.symm

theorem normalized_first_exit : normalizedWeight (chain coloredExit) 0 false = 1 / 2 := by
  rw [normalizedWeight, least_false_zero]
  symm
  apply (ENNReal.eq_div_iff (mass_pos _ (chain_guarded coloredExit) _).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (mass_le_one _ _))).2
  apply (ENNReal.mul_right_inj (survivalWeight_ne_zero 0) (survivalWeight_ne_top 0)).mp
  rw [← mul_assoc, scaled_mass, pow_zero, one_mul, exit,
    ENNReal.mul_div_cancel (survivalWeight_ne_zero 0) (survivalWeight_ne_top 0),
    pow_one, one_div]

theorem unfolded_first_exit :
    step (chain coloredExit) (normalizedWeight (chain coloredExit)) 0 false = 1 / 3 := by
  rw [chain_step]
  have h : normalizedWeight (chain coloredExit) 1 false = 0 := by
    rw [normalizedWeight, least_false_succ 0, ENNReal.zero_div]
  rw [show 0 + 1 = 1 by rfl, h, mul_zero, add_zero]
  rw [show coloredExit 0 = false by rfl, ite_eq_left rfl]
  apply (ENNReal.eq_div_iff (by norm_num) (by simp)).2
  rw [← two_mul_weight_zero, mul_assoc, exit,
    ENNReal.mul_div_cancel (survivalWeight_ne_zero 0) (survivalWeight_ne_top 0), pow_one,
    ENNReal.mul_inv_cancel (by norm_num) (by simp)]

theorem normalized_not_fixpoint :
    step (chain coloredExit) (normalizedWeight (chain coloredExit)) 0 false ≠
      normalizedWeight (chain coloredExit) 0 false := by
  rw [unfolded_first_exit, normalized_first_exit]
  exact ne_of_lt (ENNReal.div_lt_div_iff_right (by simp) (by simp) |>.2 (by norm_num))

private theorem twoPoint_map {Z W : Type*} (g : Y → Z) (h : X → W)
    (y : Y) (x : X) (p q : ℝ≥0∞) (hpq : p + q = 1) :
    (twoPoint y x p q hpq).map (Sum.map g h) = twoPoint (g y) (h x) p q hpq := by
  classical
  ext w
  rw [PMF.map_apply, Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable]
  rw [tsum_eq_single y, tsum_eq_single x]
  · cases w <;> simp
  · intro x' hx'
    simp [hx']
  · intro y' hy'
    simp [hy']

private theorem chainFrom_guarded (offset : ℕ) (label : ℕ → Y) :
    Guarded (chainFrom offset label) := by
  intro n
  refine ⟨label n, ?_⟩
  simp only [chainFrom, twoPoint_inl, ↓reduceIte, exit]
  exact ENNReal.div_pos (by simp) (survivalWeight_ne_top _)

private theorem tail_omits (I : NatIteration) (k : ℕ) :
    I.run (chain id) (chain_guarded id) (k + 1) k = 0 := by
  let shift : ℕ → ℕ := fun n => n + (k + 1)
  let tail := chainFrom (k + 1) (id : ℕ → ℕ)
  let relabeled := chainFrom (k + 1) shift
  have hnat := I.naturality tail relabeled (chainFrom_guarded _ _) (chainFrom_guarded _ _)
    shift (fun n => by
      unfold tail relabeled chainFrom
      exact twoPoint_map shift id _ _ _ _ _) 0
  have hstate := I.uniformity relabeled (chain id) (chainFrom_guarded _ _) (chain_guarded _)
    shift (fun n => by
      unfold relabeled chainFrom chain
      rw [twoPoint_map]
      rw [show shift (n + 1) = shift n + 1 by dsimp [shift]; omega]
      rfl) 0
  have heq := hnat.trans hstate
  rw [show shift 0 = k + 1 by simp [shift]] at heq
  rw [← heq, PMF.map_apply]
  have hne (a : ℕ) : k ≠ shift a := by dsimp [shift]; omega
  simp [hne]

theorem no_nat_iteration : IsEmpty NatIteration := by
  constructor
  intro I
  let f := chain (id : ℕ → ℕ)
  let g : ℕ → ℕ → ℝ≥0∞ := fun n y => I.run f (chain_guarded _) n y
  have hfix : step f g = g := I.fixpoint f (chain_guarded _)
  have h (k d n : ℕ) (hd : n + d = k + 1) :
      survivalWeight n * g n k = if d = 0 then 0 else (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
    induction d generalizing n with
    | zero =>
      have hn : n = k + 1 := by omega
      subst n
      change survivalWeight (k + 1) * I.run f _ (k + 1) k = _
      rw [tail_omits I k, mul_zero, ite_eq_left rfl]
    | succ d ih =>
      rw [← congrFun (congrFun hfix n) k, scaled_step, ih (n + 1) (by omega)]
      cases d with
      | zero =>
        have hn : n = k := by omega
        subst n
        simp
      | succ d =>
        have hn : k ≠ n := by omega
        simp [hn]
  have hscaled (k : ℕ) : survivalWeight 0 * g 0 k = (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
    simpa using h k (k + 1) 0 (by simp)
  have hsum : (∑' k, g 0 k) = 1 := (I.run f _ 0).tsum_coe
  have hweight : survivalWeight 0 = 1 := by
    calc
      survivalWeight 0 = ∑' k, survivalWeight 0 * g 0 k := by
        rw [ENNReal.tsum_mul_left, hsum, mul_one]
      _ = 1 := by
        simp only [hscaled, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two,
          inv_inv, ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)]
  have hhalf : (2⁻¹ : ℝ≥0∞) = 0 := by
    apply (ENNReal.add_left_inj ENNReal.one_ne_top).mp
    simp [survivalWeight] at hweight
  exact (by simp : (2⁻¹ : ℝ≥0∞) ≠ 0) hhalf

end Silmaril.Calco2019.Examples.Probability.Proofs
