module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Regularity

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Computation

open Silmaril.Logic.TypeTheory.IntensionalMLTT

noncomputable def conversion_upSub {n m : ℕ} {σ τ : Fin n → Term m}
    (h : ∀ i, Conversion (σ i) (τ i)) :
    ∀ i, Conversion (Term.upSub σ i) (Term.upSub τ i) := by
  intro i
  cases i using Fin.cases with
  | zero => exact .refl _
  | succ i => exact (h i).rename Fin.succ

noncomputable def conversion_subst_congr {n m : ℕ} (t : Term n) {σ τ : Fin n → Term m}
    (h : ∀ i, Conversion (σ i) (τ i)) : Conversion (t.subst σ) (t.subst τ) := by
  induction t generalizing m with
  | var i => exact h i
  | univ i => exact .refl _
  | empty => exact .refl _
  | unit => exact .refl _
  | star => exact .refl _
  | nat => exact .refl _
  | zero => exact .refl _
  | succ t ih => exact .congr_succ (ih h)
  | pi A B ihA ihB => exact .congr_pi (ihA h) (ihB (conversion_upSub h))
  | sigma A B ihA ihB => exact .congr_sigma (ihA h) (ihB (conversion_upSub h))
  | lam A body ihA ihBody => exact .congr_lam (ihA h) (ihBody (conversion_upSub h))
  | app f a ihf iha => exact .congr_app (ihf h) (iha h)
  | pair a b iha ihb => exact .congr_pair (iha h) (ihb h)
  | fst p ihp => exact .congr_fst (ihp h)
  | snd p ihp => exact .congr_snd (ihp h)
  | natrec C z s t ihC ihz ihs iht =>
    exact .congr_natrec (ihC (conversion_upSub h)) (ihz h) (ihs h) (iht h)
  | absurd A e ihA ihe => exact .congr_absurd (ihA h) (ihe h)
  | id A a b ihA iha ihb => exact .congr_id (ihA h) (iha h) (ihb h)
  | refl a iha => exact .congr_refl (iha h)
  | j A a C d b p ihA iha ihC ihd ihb ihp =>
    exact .congr_j (ihA h) (iha h) (ihC (conversion_upSub (conversion_upSub h)))
      (ihd h) (ihb h) (ihp h)

noncomputable def conversion_instantiate {n : ℕ} (t : Term (n + 1)) {a b : Term n}
    (h : Conversion a b) : Conversion (t.instantiate a) (t.instantiate b) := by
  apply conversion_subst_congr
  intro i
  cases i using Fin.cases with
  | zero => exact h
  | succ i => exact .refl _

theorem snd_pair_typed {n i j : ℕ} {Γ : Context n} {A a b : Term n} {B : Term (n + 1)}
    (hA : Derivation Γ A (.univ i)) (hB : Derivation (Γ.snoc A) B (.univ j))
    (ha : Derivation Γ a A) (hb : Derivation Γ b (B.instantiate a)) :
    TypedEq Γ (.snd (.pair a b)) b (B.instantiate (.fst (.pair a b))) := by
  have hp : Derivation Γ (.pair a b) (.sigma A B) := .pair hA hB ha hb
  have hFirst : Derivation Γ (.fst (.pair a b)) A := .fst hp
  have hTarget : Derivation Γ (B.instantiate (.fst (.pair a b))) (.univ j) :=
    hB.instantiate hA.context hFirst
  have hb' : Derivation Γ b (B.instantiate (.fst (.pair a b))) :=
    .conv hb hTarget (conversion_instantiate B (.symm (.fst_pair a b)))
  exact ⟨⟨.snd hp⟩, ⟨hb'⟩, ⟨.snd_pair a b⟩⟩

theorem natStep_result {n : ℕ} (C : Term (n + 1)) (t r : Term n) :
    ((C.subst (Fin.cons (.succ (.var 1)) (fun i => .var i.succ.succ))).subst
      (Term.upSub (Fin.cons t Term.var))).instantiate r = C.instantiate (.succ t) := by
  simp only [Term.instantiate, Term.subst_comp]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero =>
    change .succ (t.weaken.instantiate r) = Term.succ t
    rw [Term.instantiate_weaken]
  | succ i => rfl

noncomputable def natStep_apply {n : ℕ} {Γ : Context n} {C : Term (n + 1)} {s t r : Term n}
    (hs : Derivation Γ s C.natStepType) (ht : Derivation Γ t .nat)
    (hr : Derivation Γ r (C.instantiate t)) :
    Derivation Γ (.app (.app s t) r) (C.instantiate (.succ t)) := by
  have hf : Derivation Γ (.app s t)
      (.pi (C.instantiate t) ((C.subst
        (Fin.cons (.succ (.var 1)) (fun i => .var i.succ.succ))).subst
          (Term.upSub (Fin.cons t Term.var)))) := .app hs ht
  simpa only [natStep_result] using Derivation.app hf hr

theorem nat_succ_typed {n i : ℕ} {Γ : Context n} {C : Term (n + 1)} {z s t : Term n}
    (hC : Derivation (Γ.snoc .nat) C (.univ i))
    (hz : Derivation Γ z (C.instantiate .zero)) (hs : Derivation Γ s C.natStepType)
    (ht : Derivation Γ t .nat) :
    TypedEq Γ (.natrec C z s (.succ t)) (.app (.app s t) (.natrec C z s t))
      (C.instantiate (.succ t)) :=
  ⟨⟨.natrec hC hz hs (.succ ht)⟩, ⟨natStep_apply hs ht (.natrec hC hz hs ht)⟩,
    ⟨.nat_succ C z s t⟩⟩

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Computation
