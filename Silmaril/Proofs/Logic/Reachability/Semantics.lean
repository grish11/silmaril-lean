module

public import Silmaril.Logic.Reachability.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Reachability
open CategoryTheory Silmaril.Logic.Institution
variable {S : Type} {cfg : S} {A B : Signature cfg}

/-- Unary matching application is exactly predecessor image for the stored step. -/
theorem application_step (M : Model cfg A) (X : Set (M.carrier cfg)) (w : M.carrier cfg) :
    w ∈ Matching.FixedPoint.application M A.step (fun _ => X) ↔ ∃ v, step cfg M w v ∧ v ∈ X := by
  constructor
  · rintro ⟨args, hall, hop⟩
    have he : args = (fun _ => args 0) := funext fun i => congrArg args (Subsingleton.elim i 0)
    exact ⟨args 0, by exact (congrArg (fun a => w ∈ M.operation A.step a) he).mp hop, hall 0⟩
  · rintro ⟨v, hr, hv⟩
    exact ⟨fun _ => v, fun _ => hv, hr⟩

theorem terminal_step (M : Model cfg A) (w : M.carrier cfg) :
    w ∈ Matching.FixedPoint.dualApplication M A.step (fun _ => (∅ : Set (M.carrier cfg))) ↔
      ∀ v, ¬ step cfg M w v := by
  classical
  change (¬ w ∈ Matching.FixedPoint.application M A.step (fun _ => (∅ : Set (M.carrier cfg))ᶜ)) ↔ _
  simp only [Set.compl_empty]
  rw [application_step]
  simp only [Set.mem_univ, and_true, not_exists]

theorem allPartial_iff_no_bad {W : Type} (R : W → W → Prop) (Q : W → Prop) (w : W) :
    AllPartial R Q w ↔ ¬ CTL.Until R (fun x => ¬ Q x) (fun x => (∀ v, ¬ R x v) ∧ ¬ Q x) w := by
  classical
  constructor
  · intro h hu
    obtain ⟨n, path, h0, hq, hall⟩ := (CTL.until_iff_finite_prefix _ _ _ w).mp hu
    obtain ⟨i, hi, htarget⟩ := h n path h0 (fun i hi => (hall i hi).2) hq.1
    rcases Nat.eq_or_lt_of_le hi with he | hlt
    · exact hq.2 (he ▸ htarget)
    · exact (hall i hlt).1 htarget
  · intro h n path h0 hr hd
    by_contra hnone
    have avoid (i : Nat) (hi : i ≤ n) : ¬ Q (path i) := fun hq => hnone ⟨i, hi, hq⟩
    exact h ((CTL.until_iff_finite_prefix _ _ _ w).mpr
      ⟨n, path, h0, ⟨hd, avoid n le_rfl⟩, fun i hi => ⟨avoid i (Nat.le_of_lt hi), hr i hi⟩⟩)

theorem reachPattern_correct {k : Nat} {Γ : Fin k → S} (M : Model cfg A)
    (q : Matching.FirstOrder.Pattern A.algebra Γ cfg) (v : ∀ i, M.carrier (Γ i)) (w : M.carrier cfg) :
    w ∈ (reachPattern cfg q).denote M v (fun i => i.elim0) ↔
      Reaches (step cfg M) (fun x => x ∈ M.denote v q) w := by
  change w ∈ (((Matching.FixedPoint.Pattern.disj (.base q) (.app A.step (fun _ => .setvar 0))).denote M v).comp
    (Matching.FixedPoint.insert A.algebra M (P' := fun _ : Fin 1 => cfg) (fun i => i.elim0))).lfp ↔ _
  symm
  apply CTL.until_iff_lfp
  intro X x
  change (x ∈ M.denote v q ∨ x ∈ Matching.FixedPoint.application M A.step (fun _ => X)) ↔ _
  rw [application_step]
  simp only [true_and]

theorem divergePattern_correct {k : Nat} {Γ : Fin k → S} (M : Model cfg A)
    (v : ∀ i, M.carrier (Γ i)) (w : M.carrier cfg) :
    w ∈ (divergePattern cfg (A := A) (Γ := Γ)).denote M v (fun i => i.elim0) ↔ Diverges (step cfg M) w := by
  change w ∈ (((Matching.FixedPoint.Pattern.app A.step (fun _ => Matching.FixedPoint.Pattern.setvar 0)).denote M v).comp
    (Matching.FixedPoint.insert A.algebra M (P' := fun _ : Fin 1 => cfg) (fun i => i.elim0))).gfp ↔ _
  symm
  apply CTL.globally_iff_gfp
  intro X x
  change (x ∈ Matching.FixedPoint.application M A.step (fun _ => X)) ↔ _
  rw [application_step]
  simp only [true_and]

theorem badPattern_correct {k : Nat} {Γ : Fin k → S} (M : Model cfg A)
    (q : Matching.FirstOrder.Pattern A.algebra Γ cfg) (v : ∀ i, M.carrier (Γ i)) (w : M.carrier cfg) :
    w ∈ (badPattern cfg q).denote M v (fun i => i.elim0) ↔
      CTL.Until (step cfg M) (fun x => x ∉ M.denote v q)
        (fun x => (∀ y, ¬ step cfg M x y) ∧ x ∉ M.denote v q) w := by
  change w ∈ ((Matching.FixedPoint.Pattern.disj
    (.conj (.dualApp A.step (fun _ => .base Matching.FirstOrder.Pattern.bottom)) (.base (.neg q)))
    (.conj (.base (.neg q)) (.app A.step (fun _ => .setvar 0)))).denote M v |>.comp
    (Matching.FixedPoint.insert A.algebra M (P' := fun _ : Fin 1 => cfg) (fun i => i.elim0))).lfp ↔ _
  symm
  apply CTL.until_iff_lfp
  intro X x
  change ((x ∈ Matching.FixedPoint.dualApplication M A.step (fun _ => M.denote v Matching.FirstOrder.Pattern.bottom) ∧ x ∉ M.denote v q) ∨
    (x ∉ M.denote v q ∧ x ∈ Matching.FixedPoint.application M A.step (fun _ => X))) ↔ _
  rw [Matching.FirstOrder.Model.denote_bottom, terminal_step, application_step]

theorem dual_closed {k : Nat} {Γ : Fin k → S} (M : Model cfg A)
    (p : Pattern cfg (A := A) Γ) (v : ∀ i, M.carrier (Γ i)) :
    p.dual.denote M v (fun i => i.elim0) = (p.denote M v (fun i => i.elim0))ᶜ := by
  have he : (fun i : Fin 0 => (((fun i => i.elim0) i : Set (M.carrier cfg)))ᶜ) = (fun i => i.elim0) :=
    funext fun i => i.elim0
  simpa only [he] using p.denote_dual M v (fun i => i.elim0)

theorem outcome_correct (M : Model cfg A) (p : Sentence cfg A)
    (v : ∀ i, M.carrier (p.context i)) (w : M.carrier cfg) :
    w ∈ (outcomePattern cfg p).denote M v (fun i => i.elim0) ↔
      p.mode.Holds (step cfg M) (fun x => x ∈ M.denote v p.post) w := by
  unfold outcomePattern
  cases hm : p.mode with
  | finite => exact reachPattern_correct M p.post v w
  | onePath => exact or_congr (reachPattern_correct M p.post v w) (divergePattern_correct M v w)
  | allPath =>
      change w ∈ (badPattern cfg p.post).dual.denote M v (fun i => i.elim0) ↔ _
      rw [dual_closed]
      exact (not_congr (badPattern_correct M p.post v w)).trans (allPartial_iff_no_bad _ _ w).symm

theorem encode_correct (M : Model cfg A) (p : Sentence cfg A) :
    Matching.FixedPoint.Sentence.Satisfies M (encode cfg p) ↔ p.Satisfies cfg M := by
  classical
  constructor
  · intro h v w hp
    have ht := h v (fun i => i.elim0) w
    change w ∉ M.denote v p.pre ∨ w ∈ (outcomePattern cfg p).denote M v (fun i => i.elim0) at ht
    exact (outcome_correct M p v w).mp (ht.resolve_left (not_not.mpr hp))
  · intro h v η w
    change w ∉ M.denote v p.pre ∨ w ∈ (outcomePattern cfg p).denote M v η
    have he : η = (fun i => i.elim0) := funext fun i => i.elim0
    rw [he]
    by_cases hp : w ∈ M.denote v p.pre
    · exact Or.inr ((outcome_correct M p v w).mpr (h v w hp))
    · exact Or.inl hp

end Silmaril.Logic.Reachability
