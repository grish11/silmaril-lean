module

public import Silmaril.Logic.SAT.Institution.Defs
import Silmaril.Proofs.Logic.SAT.Institution.Evaluation

public section

namespace Silmaril.Proofs.Logic.SAT.Institution

open Silmaril.Logic.SAT.Institution

universe u v
variable {A : Type u} {B : Type v}

theorem exists_completion (v : PartialValuation A) : ∃ t, Completes v t := by
  refine ⟨fun a => (v a).getD false, ?_⟩
  intro a b h
  simp [h]

theorem superEval_eq_some (v : PartialValuation A) (F : Problem A) (b : Bool) :
    F.superEval v = some b ↔ ∀ t, Completes v t → F.eval t = b := by
  classical
  by_cases ht : ∀ t, Completes v t → F.eval t = true
  · have hf : ¬ ∀ t, Completes v t → F.eval t = false := by
      obtain ⟨t, hc⟩ := exists_completion v
      intro hf
      exact Bool.noConfusion ((ht t hc).symm.trans (hf t hc))
    rw [Problem.superEval, ite_eq_left ht]
    cases b with
    | false => simp [hf]
    | true => exact ⟨fun _ => ht, fun _ => rfl⟩
  · cases b <;> simp [Problem.superEval, ht]

theorem superEval_eq_none (v : PartialValuation A) (F : Problem A) :
    F.superEval v = none ↔
      (∃ t, Completes v t ∧ F.eval t = true) ∧ (∃ t, Completes v t ∧ F.eval t = false) := by
  classical
  have witness (b : Bool) : (¬ ∀ t, Completes v t → F.eval t = b) ↔
      ∃ t, Completes v t ∧ F.eval t = !b := by
    simp only [Classical.not_forall]
    apply exists_congr
    intro t
    cases b <;> cases F.eval t <;> simp
  have ht := witness false
  have hf := witness true
  simp only [Bool.not_false] at ht
  simp only [Bool.not_true] at hf
  rw [← ht, ← hf, ← superEval_eq_some, ← superEval_eq_some]
  rcases F.superEval v with _ | (_ | _) <;> simp

theorem superEval_total (t : TotalValuation A) (F : Problem A) :
    F.superEval (some ∘ t) = some (F.eval t) := by
  apply (superEval_eq_some _ _ _).2
  intro s hs
  have h : s = t := funext fun a => hs a (t a) rfl
  rw [h]

theorem evalK3_informationLE_superEval (v : PartialValuation A) (F : Problem A) :
    K3.InformationLE (F.evalK3 v) (F.superEval v) := by
  intro b hb
  apply (superEval_eq_some _ _ _).2
  intro t ht
  have hv (a : A) : K3.InformationLE (v a) ((some ∘ t) a) :=
    fun c hc => congrArg some (ht a c hc)
  have h := evalK3_informationLE hv F b hb
  rw [evalK3_total] at h
  exact Option.some.inj h

theorem completes_reduct (f : A → B) {v : PartialValuation B} {t : TotalValuation B}
    (h : Completes v t) : Completes (reduct f v) (reduct f t) :=
  fun a b hb => h (f a) b hb

theorem completion_lifts_iff (f : A → B) (v : PartialValuation B) {s : TotalValuation A}
    (hs : Completes (reduct f v) s) :
    (∃ t, Completes v t ∧ reduct f t = s) ↔
      ∀ a a', f a = f a' → s a = s a' := by
  classical
  constructor
  · rintro ⟨t, _, rfl⟩ a a' h
    exact congrArg t h
  · intro h
    let t : TotalValuation B := fun b =>
      if preimage : ∃ a, f a = b then s (Classical.choose preimage) else (v b).getD false
    refine ⟨t, ?_, ?_⟩
    · intro b c hc
      unfold t
      split
      · rename_i preimage
        apply hs (Classical.choose preimage) c
        simpa only [reduct, Function.comp_apply, Classical.choose_spec preimage] using hc
      · simp [hc]
    · funext a
      have preimage : ∃ a', f a' = f a := ⟨a, rfl⟩
      change t (f a) = s a
      rw [show t (f a) = s (Classical.choose preimage) from dite_eq_left preimage]
      exact h _ a (Classical.choose_spec preimage)

theorem superEval_rename_of_injective (f : A → B) (hf : Function.Injective f)
    (v : PartialValuation B) (F : Problem A) :
    (F.rename f).superEval v = F.superEval (reduct f v) := by
  have known (b : Bool) : (F.rename f).superEval v = some b ↔
      F.superEval (reduct f v) = some b := by
    simp only [superEval_eq_some, eval_rename]
    constructor
    · intro h s hs
      obtain ⟨t, ht, rfl⟩ := (completion_lifts_iff f v hs).2 fun a a' h => congrArg s (hf h)
      exact h t ht
    · exact fun h t ht => h (reduct f t) (completes_reduct f ht)
  cases hl : (F.rename f).superEval v with
  | some b => exact ((known b).1 hl).symm
  | none =>
    cases hr : F.superEval (reduct f v) with
    | none => rfl
    | some b => nomatch hl.symm.trans ((known b).2 hr)

theorem superEval_rename_informationLE (f : A → B) (v : PartialValuation B) (F : Problem A) :
    K3.InformationLE (F.superEval (reduct f v)) ((F.rename f).superEval v) := by
  intro b hb
  apply (superEval_eq_some _ _ _).2
  intro t ht
  rw [eval_rename]
  exact (superEval_eq_some _ _ _).1 hb _ (completes_reduct f ht)

end Silmaril.Proofs.Logic.SAT.Institution
