module

public import Silmaril.Semantics.Calco2019.Examples.Probability.Subdistribution.Defs
public import Silmaril.Semantics.Calco2019.CompleteElgot.Thms

public section

open scoped ENNReal Classical

universe u

namespace Silmaril.Calco2019.Examples.Probability.Subdist.Proofs

open Silmaril.Elgot

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type u}

private theorem left_unit (x : X) (k : X → Subdist Y) : pure x >>= k = k x := by
  ext y
  rw [bind_apply, tsum_eq_single x]
  · simp [pure_apply]
  · intro a ha
    simp [pure_apply, ha]

private theorem right_unit (p : Subdist X) : p >>= pure = p := by
  ext y
  rw [bind_apply, tsum_eq_single y]
  · simp [pure_apply]
  · intro a ha
    simp [pure_apply, Ne.symm ha]

private theorem associativity (p : Subdist X) (k : X → Subdist Y) (l : Y → Subdist Z) :
    (p >>= k) >>= l = p >>= fun x => k x >>= l := by
  ext z
  simp only [bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact tsum_comm

theorem lawful : LawfulMonad Subdist.{u} :=
  LawfulMonad.mk'
    (bind_pure_comp := fun _ _ => rfl)
    (id_map := right_unit)
    (pure_bind := left_unit)
    (bind_assoc := associativity)

local instance : LawfulMonad Subdist.{u} := lawful

theorem countable_support (p : Subdist X) : (Function.support p.weight).Countable :=
  Summable.countable_support_ennreal (ne_top_of_le_ne_top ENNReal.one_ne_top p.mass_le_one)

private theorem bottom_bind (k : X → Subdist Y) : bottom >>= k = bottom := by
  ext y
  simp [bind_apply]

private theorem unfold_weight (f : X → Subdist (Y ⊕ X)) (g : X → Subdist Y) (x : X) (y : Y) :
    unfoldLoop f g x y = f x (.inl y) + ∑' z, f x (.inr z) * g z y := by
  change (f x >>= Sum.elim pure g) y = _
  rw [bind_apply, Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable]
  congr 1
  rw [tsum_eq_single y]
  · simp [pure_apply]
  · intro a ha
    simp [pure_apply, Ne.symm ha]

private theorem unfold_mono (f : X → Subdist (Y ⊕ X)) : Monotone (unfoldLoop f) := by
  intro g h hle x y
  rw [unfold_weight, unfold_weight]
  exact add_le_add_right (tsum_le_tsum fun z => mul_le_mul_right (hle z y) _) _

theorem unfoldFor_mono (f : X → Subdist (Y ⊕ X)) : Monotone (unfoldFor f) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact fun _ _ => zero_le
  | succ n ih => exact unfold_mono f ih

/-- Iterate a subdistribution loop by its finite observations. -/
@[expose] noncomputable def solve (f : X → Subdist (Y ⊕ X)) (x : X) : Subdist Y :=
  limit (fun n => unfoldFor f n x) (fun _ _ h => unfoldFor_mono f h x)

theorem solve_weight (f : X → Subdist (Y ⊕ X)) (x : X) (y : Y) :
    solve f x y = ⨆ n, unfoldFor f n x y :=
  rfl

theorem fix (f : X → Subdist (Y ⊕ X)) : unfoldLoop f (solve f) = solve f := by
  funext x
  ext y
  rw [unfold_weight]
  simp_rw [solve_weight, ENNReal.mul_iSup]
  rw [tsum_iSup_nat (fun n z => f x (.inr z) * unfoldFor f n z y)
    (fun _ _ h z => mul_le_mul_right (unfoldFor_mono f h z y) _), ENNReal.add_iSup]
  simp_rw [← unfold_weight]
  change (⨆ n, unfoldFor f (n + 1) x y) = _
  exact Monotone.iSup_nat_add (fun _ _ h => unfoldFor_mono f h x y) 1

theorem least_solution (f : X → Subdist (Y ⊕ X)) {g : X → Subdist Y}
    (hg : unfoldLoop f g ≤ g) : solve f ≤ g := by
  have h (n : ℕ) : unfoldFor f n ≤ g := by
    induction n with
    | zero => exact fun _ _ => zero_le
    | succ n ih => exact (unfold_mono f ih).trans hg
  exact fun x y => iSup_le fun n => h n x y

private theorem bind_limit (p : ℕ → Subdist X) (hp : Monotone p) (k : X → Subdist Y) (y : Y) :
    (limit p hp >>= k) y = ⨆ n, (p n >>= k) y := by
  simp_rw [bind_apply, limit_apply, ENNReal.iSup_mul]
  exact tsum_iSup_nat _ (fun _ _ h x => mul_le_mul_left (hp h x) _)

private theorem unfold_map_return (f : X → Subdist (Y ⊕ X)) (k : Y → Subdist Z) (p : X → Subdist Z) :
    unfoldLoop (mapReturn f k) p = f >=> Sum.elim k p := by
  funext x
  change ((f x >>= Sum.elim (fun y => k y >>= pure ∘ Sum.inl) (pure ∘ Sum.inr)) >>=
    Sum.elim pure p) = _
  rw [bind_assoc]
  apply bind_congr
  intro s
  cases s <;> simp [Function.comp_def]

private theorem post_unfold (f : X → Subdist (Y ⊕ X)) (p : X → Subdist Y) (k : Y → Subdist Z) :
    unfoldLoop f p >=> k = unfoldLoop (mapReturn f k) (p >=> k) := by
  rw [unfold_map_return]
  funext x
  change (f x >>= Sum.elim pure p) >>= k = f x >>= Sum.elim k (p >=> k)
  rw [bind_assoc]
  apply bind_congr
  intro s
  cases s with
  | inl y => simp
  | inr x => rfl

theorem natural (f : X → Subdist (Y ⊕ X)) (k : Y → Subdist Z) :
    solve f >=> k = solve (mapReturn f k) := by
  have h (n : ℕ) : unfoldFor (mapReturn f k) n = unfoldFor f n >=> k := by
    induction n with
    | zero => exact funext fun _ => (bottom_bind k).symm
    | succ n ih =>
      change unfoldLoop (mapReturn f k) (unfoldFor (mapReturn f k) n) =
        unfoldLoop f (unfoldFor f n) >=> k
      rw [ih, post_unfold]
  funext x
  ext y
  change (solve f x >>= k) y = solve (mapReturn f k) x y
  unfold solve
  rw [bind_limit, limit_apply]
  simp only [h]
  rfl

private theorem unfold_flatten (f : X → Subdist ((Y ⊕ X) ⊕ X)) (p : X → Subdist Y) :
    unfoldLoop (flattenBody f) p = f >=> Sum.elim (Sum.elim pure p) p := by
  funext x
  change ((f x >>= pure ∘ flatten) >>= Sum.elim pure p) = _
  rw [bind_assoc]
  apply bind_congr
  intro s
  cases s <;> simp [flatten]

private theorem unfold_twice (f : X → Subdist ((Y ⊕ X) ⊕ X))
    (h : X → Subdist (Y ⊕ X)) (p : X → Subdist Y) :
    unfoldLoop (unfoldLoop f h) p = f >=> Sum.elim (Sum.elim pure p) (unfoldLoop h p) := by
  funext x
  change ((f x >>= Sum.elim pure h) >>= Sum.elim pure p) = _
  rw [bind_assoc]
  apply bind_congr
  intro s
  cases s with
  | inl y => simp
  | inr x => rfl

theorem diagonal (f : X → Subdist ((Y ⊕ X) ⊕ X)) :
    solve (solve f) = solve (flattenBody f) := by
  let h := solve f
  let p := solve h
  let q := solve (flattenBody f)
  have hh : unfoldLoop f h = h := fix f
  have hp : unfoldLoop h p = p := fix h
  have hq : unfoldLoop (flattenBody f) q = q := fix _
  apply le_antisymm
  · apply least_solution h
    change h >=> Sum.elim pure q ≤ q
    rw [natural]
    apply least_solution
    rw [unfold_map_return, ← unfold_flatten, hq]
  · apply least_solution (flattenBody f)
    have he := unfold_twice f h p
    rw [hh, hp] at he
    rw [unfold_flatten, ← he]

theorem uniform (f : X → Subdist (Y ⊕ X)) (g : Z → Subdist (Y ⊕ Z)) (h : Z → X)
    (comm : f ∘ h = g >=> liftPure (Sum.map id h)) : solve f ∘ h = solve g := by
  have hs (p : X → Subdist Y) : unfoldLoop f p ∘ h = unfoldLoop g (p ∘ h) := by
    funext z
    have hz := congrFun comm z
    change (f (h z) >>= Sum.elim pure p) = g z >>= Sum.elim pure (p ∘ h)
    change f (h z) = g z >>= pure ∘ Sum.map id h at hz
    rw [hz, bind_assoc]
    apply bind_congr
    intro s
    cases s <;> simp [Function.comp_def]
  have hfin (n : ℕ) : unfoldFor f n ∘ h = unfoldFor g n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change unfoldLoop f (unfoldFor f n) ∘ h = unfoldLoop g (unfoldFor g n)
      rw [hs, ih]
  funext z
  ext y
  simp only [Function.comp_apply, solve_weight]
  exact iSup_congr fun n => congrArg (fun v : Subdist Y => v y) (congrFun (hfin n) z)

private theorem pmf_unfold (f : X → PMF (Y ⊕ X)) (n : ℕ) (x : X) (y : Y) :
    unfoldFor (fun x => ofPMF (f x)) n x y = Probability.approx f n x y := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change unfoldLoop (fun x => ofPMF (f x)) (unfoldFor (fun x => ofPMF (f x)) n) x y = _
    rw [unfold_weight, Probability.approx, Probability.step]
    simp only [ofPMF_apply, ih]

theorem pmf_agreement (f : X → PMF (Y ⊕ X)) (x : X) (y : Y) :
    solve (fun x => ofPMF (f x)) x y = Probability.least f x y := by
  rw [solve_weight, Probability.least]
  exact iSup_congr fun n => pmf_unfold f n x y

noncomputable local instance : Iterate Subdist.{u} := ⟨solve⟩

theorem lawfulElgot : LawfulElgotMonad Subdist.{u} where
  fixpoint f := (fix f).symm
  naturality := natural
  codiagonal := diagonal
  uniformity f g h comm := by
    have comm' : g ∘ h = f >=> liftPure (Sum.map id h) := by
      funext z
      have hz := congrFun comm z
      change (f z >>= liftPure (Sum.map id h)) = pure (h z) >>= g at hz
      change g (h z) = f z >>= liftPure (Sum.map id h)
      simpa only [pure_bind] using hz.symm
    funext z
    have hz := congrFun (uniform g f h comm') z
    change solve f z = pure (h z) >>= solve g
    simpa only [pure_bind, Function.comp_apply] using hz.symm

end Silmaril.Calco2019.Examples.Probability.Subdist.Proofs
