module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Computation

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRecursorSubjectReduction

open Silmaril.Logic.TypeTheory.IntensionalMLTT

private def IsRecursor {n : ℕ} : Term n → Prop
  | .natrec _ _ _ _ | .j _ _ _ _ _ _ => True
  | _ => False

private theorem root_subjectReduction {n : ℕ} {Γ : Context n} {t T : Term n}
    (h : Derivation Γ t T) : ∀ u, RootReduction t u → IsRecursor t → Typing Γ u T := by
  induction h using Derivation.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc _ _ _ _ => trivial
  | natrec hC hz hs ht _ _ _ _ =>
    intro u hr _
    cases hr with
    | nat_zero => exact ⟨hz⟩
    | nat_succ =>
      obtain ⟨hpred⟩ := (Derivation.succ_generation ht).1
      exact (TypedEq.nat_succ hC hz hs hpred).2.1
  | j hA ha hC hd hb hp _ _ _ _ _ _ =>
    intro u hr _
    cases hr
    exact ⟨hd⟩
  | conv ht hB hAB iht _ =>
    intro u hr hshape
    obtain ⟨hu⟩ := iht u hr hshape
    exact ⟨.conv hu hB hAB⟩
  | cumulative hA hij ihA =>
    intro u hr hshape
    obtain ⟨hu⟩ := ihA u hr hshape
    exact ⟨.cumulative hu hij⟩
  | _ => intro u hr hshape; cases hshape

theorem nat_zero_subjectReduction {n : ℕ} {Γ : Context n} {T z s : Term n} {C : Term (n + 1)}
    (h : Derivation Γ (.natrec C z s .zero) T) : Typing Γ z T :=
  root_subjectReduction h z (.nat_zero C z s) trivial

theorem nat_succ_subjectReduction {n : ℕ} {Γ : Context n} {T z s t : Term n} {C : Term (n + 1)}
    (h : Derivation Γ (.natrec C z s (.succ t)) T) :
    Typing Γ (.app (.app s t) (.natrec C z s t)) T :=
  root_subjectReduction h _ (.nat_succ C z s t) trivial

theorem j_refl_subjectReduction {n : ℕ} {Γ : Context n} {T A a d : Term n} {C : Term (n + 2)}
    (h : Derivation Γ (.j A a C d a (.refl a)) T) : Typing Γ d T :=
  root_subjectReduction h d (.j_refl A a C d) trivial

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRecursorSubjectReduction
