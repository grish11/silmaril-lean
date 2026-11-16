module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Codes.Thms

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodeInversion

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability


theorem univ_inv {i j : ℕ} {X : Set (Value 0)} (h : Code i (univ j) X) :
    j < i ∧ X = {q | ∃ Y, Code j q Y} := by
  have hLayer : CodeLayer i (fun k _ => Code k) (univ j) X := Code.iff_layer.mp h
  generalize heq : univ j = q at hLayer
  cases hLayer with
  | univ k hk =>
    have hjk : j = k := univ_inj heq
    cases hjk
    exact ⟨hk, rfl⟩
  | _ =>
    have hHead := congrArg head heq
    exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
      head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])

theorem pi_inv {i : ℕ} {A : Value 0} {B : Value 1} {T : Set (Value 0)}
    (h : Code i (pi A B) T) :
    ∃ X Y, Code i A X ∧ (∀ a ∈ X, Code i (instantiate B a) (Y a)) ∧ T = FunctionSpace X Y := by
  have hLayer : CodeLayer i (fun k _ => Code k) (pi A B) T := Code.iff_layer.mp h
  generalize heq : pi A B = q at hLayer
  cases hLayer with
  | @pi A' B' X Y hA hB =>
    obtain ⟨hAA, hBB⟩ := pi_inj heq
    cases hAA
    cases hBB
    exact ⟨X, Y, Code.iff_layer.mpr hA, (fun a ha => Code.iff_layer.mpr (hB a ha)), rfl⟩
  | _ =>
    have hHead := congrArg head heq
    exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
      head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])

theorem sigma_inv {i : ℕ} {A : Value 0} {B : Value 1} {T : Set (Value 0)}
    (h : Code i (sigma A B) T) :
    ∃ X Y, Code i A X ∧ (∀ a ∈ X, Code i (instantiate B a) (Y a)) ∧ T = PairSpace X Y := by
  have hLayer : CodeLayer i (fun k _ => Code k) (sigma A B) T := Code.iff_layer.mp h
  generalize heq : sigma A B = q at hLayer
  cases hLayer with
  | @sigma A' B' X Y hA hB =>
    obtain ⟨hAA, hBB⟩ := sigma_inj heq
    cases hAA
    cases hBB
    exact ⟨X, Y, Code.iff_layer.mpr hA, (fun a ha => Code.iff_layer.mpr (hB a ha)), rfl⟩
  | _ =>
    have hHead := congrArg head heq
    exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
      head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])

theorem id_inv {i : ℕ} {A a b : Value 0} {T : Set (Value 0)}
    (h : Code i (id A a b) T) :
    ∃ X, Code i A X ∧ a ∈ X ∧ b ∈ X ∧ T = IdentitySpace a b := by
  have hLayer : CodeLayer i (fun k _ => Code k) (id A a b) T := Code.iff_layer.mp h
  generalize heq : id A a b = q at hLayer
  cases hLayer with
  | @id A' a' b' X hA ha hb =>
    obtain ⟨hAA, haa, hbb⟩ := id_inj heq
    cases hAA
    cases haa
    cases hbb
    exact ⟨X, Code.iff_layer.mpr hA, ha, hb, rfl⟩
  | _ =>
    have hHead := congrArg head heq
    exact absurd hHead (by simp only [head_nat, head_empty, head_unit, head_univ,
      head_pi, head_sigma, head_id, Option.some.injEq, reduceCtorEq, not_false_eq_true])

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodeInversion
