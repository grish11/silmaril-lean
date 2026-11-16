module

public import Silmaril.Logic.CTL.Defs
public import Mathlib.Logic.Relation

@[expose] public section
namespace Silmaril.Logic.CTL
open CategoryTheory Silmaril.Logic.Institution

theorem Until.congr {W : Type} {R : W → W → Prop} {P P' Q Q' : W → Prop}
    (hp : ∀ w, P w ↔ P' w) (hq : ∀ w, Q w ↔ Q' w) (w : W) :
    Until R P Q w ↔ Until R P' Q' w := by
  constructor
  · intro h
    induction h with
    | now h => exact .now ((hq _).mp h)
    | next hpw hr _ ih => exact .next ((hp _).mp hpw) hr ih
  · intro h
    induction h with
    | now h => exact .now ((hq _).mpr h)
    | next hpw hr _ ih => exact .next ((hp _).mpr hpw) hr ih

theorem Globally.congr {W : Type} {R : W → W → Prop} {P Q : W → Prop}
    (h : ∀ w, P w ↔ Q w) (w : W) : Globally R P w ↔ Globally R Q w := by
  constructor
  · rintro ⟨path, h0, hr, hp⟩
    exact ⟨path, h0, hr, fun n => (h _).mp (hp n)⟩
  · rintro ⟨path, h0, hr, hp⟩
    exact ⟨path, h0, hr, fun n => (h _).mpr (hp n)⟩

theorem Formula.map_id {S : Signature} (p : Formula S) : p.map (𝟙 S) = p := by
  induction p with
  | atom => rfl
  | bot => rfl
  | neg p hp => exact congrArg Formula.neg hp
  | conj p q hp hq => exact congrArg₂ Formula.conj hp hq
  | ex p hp => exact congrArg Formula.ex hp
  | eu p q hp hq => exact congrArg₂ Formula.eu hp hq
  | eg p hp => exact congrArg Formula.eg hp

theorem Formula.map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) (p : Formula S) :
    p.map (f ≫ g) = (p.map f).map g := by
  induction p with
  | atom => rfl
  | bot => rfl
  | neg p hp => exact congrArg Formula.neg hp
  | conj p q hp hq => exact congrArg₂ Formula.conj hp hq
  | ex p hp => exact congrArg Formula.ex hp
  | eu p q hp hq => exact congrArg₂ Formula.eu hp hq
  | eg p hp => exact congrArg Formula.eg hp

theorem Formula.holds_map {S T : Signature} (f : S ⟶ T) (M : Model T) (p : Formula S) :
    ∀ w, (p.map f).Holds M w ↔ p.Holds (reduct f M) w := by
  induction p with
  | atom => intro w; rfl
  | bot => intro w; rfl
  | neg p hp => intro w; exact not_congr (hp w)
  | conj p q hp hq => intro w; exact and_congr (hp w) (hq w)
  | ex p hp =>
      intro w
      change (∃ v, M.toModal.accessible w v ∧ (p.map f).Holds M v) ↔ _
      exact exists_congr fun v => and_congr Iff.rfl (hp v)
  | eu p q hp hq => intro w; exact Until.congr hp hq w
  | eg p hp => intro w; exact Globally.congr hp w

/-- EU unfolding is finite path decomposition, with no seriality premise. -/
theorem until_unfold {W : Type} (R : W → W → Prop) (P Q : W → Prop) (w : W) :
    Until R P Q w ↔ Q w ∨ (P w ∧ ∃ v, R w v ∧ Until R P Q v) := by
  constructor
  · intro h
    cases h with
    | now hq => exact Or.inl hq
    | next hp hr hu => exact Or.inr ⟨hp, _, hr, hu⟩
  · rintro (hq | ⟨hp, v, hr, hu⟩)
    · exact .now hq
    · exact .next hp hr hu

/-- An explicit finite-prefix witness; no infinite continuation is required. -/
theorem until_iff_finite_prefix {W : Type} (R : W → W → Prop) (P Q : W → Prop) (w : W) :
    Until R P Q w ↔ ∃ (n : Nat) (path : Nat → W), path 0 = w ∧ Q (path n) ∧
      ∀ i, i < n → P (path i) ∧ R (path i) (path (i+1)) := by
  constructor
  · show Until R P Q w → ∃ (n : Nat) (path : Nat → W), path 0 = w ∧ Q (path n) ∧
        ∀ i, i < n → P (path i) ∧ R (path i) (path (i+1))
    intro h
    induction h with
    | now hq => exact ⟨0, fun _ => _, rfl, hq, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
    | @next w v hp hr hu ih =>
        show ∃ (n : Nat) (path : Nat → W), path 0 = w ∧ Q (path n) ∧
          ∀ i, i < n → P (path i) ∧ R (path i) (path (i+1))
        obtain ⟨n, path, h0, hq, hall⟩ := ih
        refine ⟨n+1, (fun i => match i with | 0 => w | i+1 => path i), rfl, hq, ?_⟩
        intro i hi
        cases i with
        | zero =>
            change P w ∧ R w (path 0)
            exact ⟨hp, h0.symm ▸ hr⟩
        | succ i => exact hall i (Nat.lt_of_succ_lt_succ hi)
  · rintro ⟨n, path, h0, hq, hall⟩
    induction n generalizing w path with
    | zero => exact .now (h0 ▸ hq)
    | succ n ih =>
        have htail : Until R P Q (path 1) :=
          ih (path 1) (fun i => path (i+1)) rfl hq (fun i hi => hall (i+1) (Nat.succ_lt_succ hi))
        have hfirst : P w ∧ R w (path 1) := h0 ▸ hall 0 (Nat.zero_lt_succ n)
        exact .next hfirst.1 hfirst.2 htail

/-- EG unfolding splits and prepends actual infinite sequences. -/
theorem globally_unfold {W : Type} (R : W → W → Prop) (P : W → Prop) (w : W) :
    Globally R P w ↔ P w ∧ ∃ v, R w v ∧ Globally R P v := by
  constructor
  · rintro ⟨path, h0, hr, hp⟩
    exact ⟨h0 ▸ hp 0, path 1, h0 ▸ hr 0,
      (fun n => path (n+1)), rfl, (fun n => hr (n+1)), (fun n => hp (n+1))⟩
  · rintro ⟨hp, v, hr, path, h0, hs, hall⟩
    refine ⟨(fun n => match n with | 0 => w | n+1 => path n), rfl, ?_, ?_⟩
    · intro n
      cases n with
      | zero =>
          change R w (path 0)
          exact h0.symm ▸ hr
      | succ n => exact hs n
    · intro n
      cases n with
      | zero => exact hp
      | succ n => exact hall n

theorem until_true_iff_reachable {W : Type} (R : W → W → Prop) (Q : W → Prop) (w : W) :
    Until R (fun _ => True) Q w ↔ ∃ v, Relation.ReflTransGen R w v ∧ Q v := by
  constructor
  · intro h
    induction h with
    | now hq => exact ⟨_, .refl, hq⟩
    | next _ hr _ ih =>
        obtain ⟨v, hv, hq⟩ := ih
        exact ⟨v, hv.head hr, hq⟩
  · rintro ⟨v, hp, hq⟩
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl => exact .now hq
    | head hr _ ih => exact .next trivial hr ih

end Silmaril.Logic.CTL
