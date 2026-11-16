module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S} (M : Model A)

/-- The occurrence computation controls both covariant and contravariant free
set dependencies, even in the presence of nested binders. -/
theorem Pattern.denote_variance {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : Pattern A P Γ s) : ∀ (v : ObjEnv A M Γ) (η ζ : SetEnv A M P),
    (∀ i, p.occurs false i = true → η i ⊆ ζ i) →
    (∀ i, p.occurs true i = true → ζ i ⊆ η i) →
    p.denote M v η ⊆ p.denote M v ζ := by
  induction p with
  | base _ => intro _ _ _ _ _; exact le_rfl
  | setvar i => intro _ _ _ hp _; exact hp i (by simp [occurs])
  | app op args ih =>
      intro v η ζ hp hn
      apply FixedPoint.application_mono
      intro j
      apply ih j v η ζ
      · intro i hi
        exact hp i (by
          change (List.finRange _).any (fun j => (args j).occurs false i) = true
          exact List.any_eq_true.mpr ⟨j, by simp, hi⟩)
      · intro i hi
        exact hn i (by
          change (List.finRange _).any (fun j => (args j).occurs true i) = true
          exact List.any_eq_true.mpr ⟨j, by simp, hi⟩)
  | neg p ih =>
      intro v η ζ hp hn
      exact Set.compl_subset_compl.mpr (ih v ζ η hn hp)
  | conj p q ihp ihq =>
      intro v η ζ hp hn x hx
      exact ⟨ihp v η ζ (fun i hi => hp i (by simp only [occurs] at hi ⊢; simp [hi]))
          (fun i hi => hn i (by simp only [occurs] at hi ⊢; simp [hi])) hx.1,
        ihq v η ζ (fun i hi => hp i (by simp only [occurs] at hi ⊢; simp [hi]))
          (fun i hi => hn i (by simp only [occurs] at hi ⊢; simp [hi])) hx.2⟩
  | ex b p ih =>
      intro v η ζ hp hn x hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, ih (Fin.cases a v) η ζ hp hn ha⟩
  | mu p ih =>
      intro v η ζ hp hn
      apply le_sInf
      intro X hX
      apply sInf_le
      apply Set.Subset.trans _ hX
      apply ih v (Fin.cases X η) (Fin.cases X ζ)
      · intro i
        refine Fin.cases (fun _ => le_rfl) (fun j hj => hp j hj) i
      · intro i
        refine Fin.cases (fun _ => le_rfl) (fun j hj => hn j hj) i
  | nu p ih =>
      intro v η ζ hp hn
      apply sSup_le
      intro X hX
      apply le_sSup
      apply Set.Subset.trans hX
      apply ih v (Fin.cases X η) (Fin.cases X ζ)
      · intro i
        refine Fin.cases (fun _ => le_rfl) (fun j hj => hp j hj) i
      · intro i
        refine Fin.cases (fun _ => le_rfl) (fun j hj => hn j hj) i

/-- Only positivity of the bound variable is needed; other free variables may
have arbitrary and mixed polarity. -/
theorem Pattern.body_monotone {r k : Nat} {P : Fin (r+1) → S} {Γ : Fin k → S}
    (p : Pattern A P Γ (P 0)) (positive : p.occurs true 0 = false)
    (v : ObjEnv A M Γ) (η : SetEnv A M (P ∘ Fin.succ)) :
    Monotone (fun X => p.denote M v (Fin.cases X η)) := by
  intro X Y hXY
  apply p.denote_variance M v
  · intro i
    refine Fin.cases (fun _ => hXY) (fun _ _ => le_rfl) i
  · intro i
    refine Fin.cases ?_ (fun _ _ => le_rfl) i
    intro h
    simp [positive] at h

def Pattern.bodyOrderHom {r k : Nat} {P : Fin (r+1) → S} {Γ : Fin k → S}
    (p : Pattern A P Γ (P 0)) (positive : p.occurs true 0 = false)
    (v : ObjEnv A M Γ) (η : SetEnv A M (P ∘ Fin.succ)) :
    Set (M.carrier (P 0)) →o Set (M.carrier (P 0)) :=
  ⟨fun X => p.denote M v (Fin.cases X η), p.body_monotone M positive v η⟩

variable {r k : Nat} {P : Fin (r+1) → S} {Γ : Fin k → S}
    (p : Pattern A P Γ (P 0)) (positive : p.occurs true 0 = false)
    (v : ObjEnv A M Γ) (η : SetEnv A M (P ∘ Fin.succ))

include positive

theorem mu_unfold : (Pattern.mu p).denote M v η =
    p.denote M v (Fin.cases ((Pattern.mu p).denote M v η) η) :=
  (p.bodyOrderHom M positive v η).map_lfp.symm

theorem nu_unfold : (Pattern.nu p).denote M v η =
    p.denote M v (Fin.cases ((Pattern.nu p).denote M v η) η) :=
  (p.bodyOrderHom M positive v η).map_gfp.symm

theorem mu_induction (X : Set (M.carrier (P 0)))
    (h : p.denote M v (Fin.cases X η) ⊆ X) : (Pattern.mu p).denote M v η ⊆ X :=
  (p.bodyOrderHom M positive v η).lfp_le h

theorem nu_coinduction (X : Set (M.carrier (P 0)))
    (h : X ⊆ p.denote M v (Fin.cases X η)) : X ⊆ (Pattern.nu p).denote M v η :=
  (p.bodyOrderHom M positive v η).le_gfp h
end Silmaril.Logic.Matching.GeneralFixedPoint
