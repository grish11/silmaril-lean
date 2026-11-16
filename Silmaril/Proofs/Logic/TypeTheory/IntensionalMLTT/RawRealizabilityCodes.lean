module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Codes.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Algebra.Thms

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

theorem layer_functional {cap : ℕ} {lower : ∀ j, j < cap → Value 0 → Set (Value 0) → Prop}
    {q : Value 0} {X : Set (Value 0)} (h : CodeLayer cap lower q X) :
    ∀ {cap' : ℕ} {lower' : ∀ j, j < cap' → Value 0 → Set (Value 0) → Prop}
      {q' : Value 0} {X' : Set (Value 0)},
      (∀ j hj hj', lower j hj = lower' j hj') → q = q' → CodeLayer cap' lower' q' X' → X = X' := by
  induction h with
  | nat =>
    intro cap' lower' q' X' hLower heq h'
    have hHead : head (nat) = head q' := congrArg head heq
    cases h' with
    | nat => rfl
    | _ => exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
        head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])
  | empty =>
    intro cap' lower' q' X' hLower heq h'
    have hHead : head (empty) = head q' := congrArg head heq
    cases h' with
    | empty => rfl
    | _ => exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
        head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])
  | unit =>
    intro cap' lower' q' X' hLower heq h'
    have hHead : head (unit) = head q' := congrArg head heq
    cases h' with
    | unit => rfl
    | _ => exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
        head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])
  | univ j hj =>
    show ∀ {cap' : ℕ} {lower' : ∀ j, j < cap' → Value 0 → Set (Value 0) → Prop}
      {q' : Value 0} {X' : Set (Value 0)},
      (∀ j hj hj', lower j hj = lower' j hj') → (univ j) = q' →
      CodeLayer cap' lower' q' X' → {q | ∃ X, lower j hj q X} = X'
    intro cap' lower' q' X' hLower heq h'
    have hHead : head (univ j) = head q' := congrArg head heq
    cases h' with
    | univ k hk =>
      have hjk : j = k := univ_inj heq
      cases hjk
      have hRelations : lower j hj = lower' j hk := hLower j hj hk
      exact congrArg (fun R => {q | ∃ X, R q X}) hRelations
    | _ => exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
        head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])
  | @pi A B X Y hA hB ihA ihB =>
    show ∀ {cap' : ℕ} {lower' : ∀ j, j < cap' → Value 0 → Set (Value 0) → Prop}
      {q' : Value 0} {X' : Set (Value 0)},
      (∀ j hj hj', lower j hj = lower' j hj') → (pi A B) = q' →
      CodeLayer cap' lower' q' X' → FunctionSpace X Y = X'
    intro cap' lower' q' X' hLower heq h'
    have hHead : head (pi A B) = head q' := congrArg head heq
    cases h' with
    | @pi A' B' X' Y' hA' hB' =>
      show FunctionSpace X Y = FunctionSpace X' Y'
      obtain ⟨hAA, hBB⟩ := pi_inj heq
      have hXX : X = X' := ihA hLower hAA hA'
      cases hXX
      have hYY : ∀ a ∈ X, Y a = Y' a := fun a ha => ihB a ha hLower (congrArg (fun B => instantiate B a) hBB) (hB' a ha)
      apply Set.ext
      intro f
      constructor
      · intro hf a ha
        exact (hYY a ha) ▸ hf a ha
      · intro hf a ha
        exact (hYY a ha).symm ▸ hf a ha
    | _ => exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
        head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])
  | @sigma A B X Y hA hB ihA ihB =>
    show ∀ {cap' : ℕ} {lower' : ∀ j, j < cap' → Value 0 → Set (Value 0) → Prop}
      {q' : Value 0} {X' : Set (Value 0)},
      (∀ j hj hj', lower j hj = lower' j hj') → (sigma A B) = q' →
      CodeLayer cap' lower' q' X' → PairSpace X Y = X'
    intro cap' lower' q' X' hLower heq h'
    have hHead : head (sigma A B) = head q' := congrArg head heq
    cases h' with
    | @sigma A' B' X' Y' hA' hB' =>
      show PairSpace X Y = PairSpace X' Y'
      obtain ⟨hAA, hBB⟩ := sigma_inj heq
      have hXX : X = X' := ihA hLower hAA hA'
      cases hXX
      have hYY : ∀ a ∈ X, Y a = Y' a := fun a ha => ihB a ha hLower (congrArg (fun B => instantiate B a) hBB) (hB' a ha)
      apply Set.ext
      intro f
      constructor
      · rintro ⟨a, ha, b, hb, heq⟩
        exact ⟨a, ha, b, (hYY a ha) ▸ hb, heq⟩
      · rintro ⟨a, ha, b, hb, heq⟩
        exact ⟨a, ha, b, (hYY a ha).symm ▸ hb, heq⟩
    | _ => exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
        head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])
  | @id A a b X hA ha hb ihA =>
    show ∀ {cap' : ℕ} {lower' : ∀ j, j < cap' → Value 0 → Set (Value 0) → Prop}
      {q' : Value 0} {X' : Set (Value 0)},
      (∀ j hj hj', lower j hj = lower' j hj') → (id A a b) = q' →
      CodeLayer cap' lower' q' X' → IdentitySpace a b = X'
    intro cap' lower' q' X' hLower heq h'
    have hHead : head (id A a b) = head q' := congrArg head heq
    cases h' with
    | id hA' ha' hb' =>
      obtain ⟨hAA, haa, hbb⟩ := id_inj heq
      exact congrArg₂ IdentitySpace haa hbb
    | _ => exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
        head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])

theorem code_iff_layer {i : ℕ} {q : Value 0} {X : Set (Value 0)} :
    Code i q X ↔ CodeLayer i (fun k _ => Code k) q X := by rw [Code]

theorem code_functional {i j : ℕ} {q : Value 0} {X Y : Set (Value 0)}
    (hX : Code i q X) (hY : Code j q Y) : X = Y := by
  have hX' : CodeLayer i (fun k _ => Code k) q X := code_iff_layer.mp hX
  have hY' : CodeLayer j (fun k _ => Code k) q Y := code_iff_layer.mp hY
  exact layer_functional hX' (fun _ _ _ => rfl) rfl hY'
theorem code_nat (i : ℕ) : Code i nat Naturals := code_iff_layer.mpr .nat
theorem code_empty (i : ℕ) : Code i empty ∅ := code_iff_layer.mpr .empty
theorem code_unit (i : ℕ) : Code i unit Units := code_iff_layer.mpr .unit

theorem code_univ {i j : ℕ} (h : j < i) :
    Code i (univ j) {q | ∃ X, Code j q X} := code_iff_layer.mpr (.univ j h)

theorem code_pi {i : ℕ} {A : Value 0} {B : Value 1} {X : Set (Value 0)}
    {Y : Value 0 → Set (Value 0)} (hA : Code i A X)
    (hB : ∀ a ∈ X, Code i (instantiate B a) (Y a)) :
    Code i (pi A B) (FunctionSpace X Y) :=
  code_iff_layer.mpr (.pi (code_iff_layer.mp hA) (fun a ha => code_iff_layer.mp (hB a ha)))

theorem code_sigma {i : ℕ} {A : Value 0} {B : Value 1} {X : Set (Value 0)}
    {Y : Value 0 → Set (Value 0)} (hA : Code i A X)
    (hB : ∀ a ∈ X, Code i (instantiate B a) (Y a)) :
    Code i (sigma A B) (PairSpace X Y) :=
  code_iff_layer.mpr (.sigma (code_iff_layer.mp hA) (fun a ha => code_iff_layer.mp (hB a ha)))

theorem code_id {i : ℕ} {A a b : Value 0} {X : Set (Value 0)}
    (hA : Code i A X) (ha : a ∈ X) (hb : b ∈ X) : Code i (id A a b) (IdentitySpace a b) :=
  code_iff_layer.mpr (.id (code_iff_layer.mp hA) ha hb)

theorem layer_lift {i : ℕ} {lower : ∀ j, j < i → Value 0 → Set (Value 0) → Prop}
    {q : Value 0} {X : Set (Value 0)} (h : CodeLayer i lower q X) :
    ∀ {k : ℕ} {lower' : ∀ j, j < k → Value 0 → Set (Value 0) → Prop} (hik : i ≤ k),
      (∀ j hj, lower j hj = lower' j (hj.trans_le hik)) → CodeLayer k lower' q X := by
  induction h with
  | nat => intro k lower' hik hLower; exact .nat
  | empty => intro k lower' hik hLower; exact .empty
  | unit => intro k lower' hik hLower; exact .unit
  | univ j hj =>
    show ∀ {k : ℕ} {lower' : ∀ j, j < k → Value 0 → Set (Value 0) → Prop} (hik : i ≤ k),
      (∀ j hj, lower j hj = lower' j (hj.trans_le hik)) →
      CodeLayer k lower' (univ j) {q | ∃ X, lower j hj q X}
    intro k lower' hik hLower
    have hTypes : {q | ∃ X, lower j hj q X} = {q | ∃ X, lower' j (hj.trans_le hik) q X} :=
      congrArg (fun R => {q | ∃ X, R q X}) (hLower j hj)
    exact hTypes.symm ▸ CodeLayer.univ j (hj.trans_le hik)
  | pi hA hB ihA ihB =>
    intro k lower' hik hLower
    exact .pi (ihA hik hLower) (fun a ha => ihB a ha hik hLower)
  | sigma hA hB ihA ihB =>
    intro k lower' hik hLower
    exact .sigma (ihA hik hLower) (fun a ha => ihB a ha hik hLower)
  | id hA ha hb ihA => intro k lower' hik hLower; exact .id (ihA hik hLower) ha hb

theorem code_lift {i j : ℕ} {q : Value 0} {X : Set (Value 0)} (h : Code i q X) (hij : i ≤ j) :
    Code j q X := code_iff_layer.mpr (layer_lift (code_iff_layer.mp h) hij (fun _ _ => rfl))

theorem raw_conversion_invariant {i : ℕ} {A B : Term 0} {X : Set (Value 0)}
    (h : Convertible A B) (hA : Code i (ofTerm A) X) : Code i (ofTerm B) X :=
  (ofTerm_eq_iff.mpr (LinearJ.ofConvertible h)) ▸ hA

theorem empty_meaning {i : ℕ} {X : Set (Value 0)} (h : Code i empty X) : X = ∅ :=
  code_functional h (code_empty i)

theorem no_empty_realizer {i : ℕ} {X : Set (Value 0)} (h : Code i empty X) (q : Value 0) : q ∉ X := by
  rw [empty_meaning h]
  exact fun hq => hq

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes
