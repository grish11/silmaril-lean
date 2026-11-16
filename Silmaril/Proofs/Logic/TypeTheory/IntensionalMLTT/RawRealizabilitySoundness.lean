module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Soundness.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Environment.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Computation

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

theorem realizes_univ_iff {n i : ℕ} {A : Term n} {ρ : Environment n 0} :
    Realizes A (.univ i) ρ ↔ ∃ X, Code i (eval A ρ) X := by
  constructor
  · rintro ⟨k, X, hX, ha⟩
    have h := Code.univ_inv hX
    rw [h.2] at ha
    exact ha
  · rintro ⟨X, hX⟩
    exact ⟨i + 1, {q | ∃ Y, Code i q Y}, Code.univ (Nat.lt_succ_self i), X, hX⟩

theorem realizes_mem {n k : ℕ} {t A : Term n} {ρ : Environment n 0}
    {X : Set (Value 0)} (hX : Code k (eval A ρ) X) (ht : Realizes t A ρ) :
    eval t ρ ∈ X := by
  rcases ht with ⟨i, Y, hY, ht⟩
  rw [Code.functional hY hX] at ht
  exact ht

theorem context_cons {n i : ℕ} {Γ : Context n} {A : Term n} {ρ : Environment n 0}
    {X : Set (Value 0)} {a : Value 0} (hρ : RealizesContext Γ ρ)
    (hA : Code i (eval A ρ) X) (ha : a ∈ X) :
    RealizesContext (Γ.snoc A) (Fin.cons a ρ) := by
  simpa only [RealizesContext, Fin.tail_cons, Fin.cons_zero] using
    And.intro hρ (show ∃ j Y, Code j (eval A ρ) Y ∧ a ∈ Y from ⟨i, X, hA, ha⟩)

theorem lookup {n : ℕ} {Γ : Context n} {i : Fin n} {A : Term n} (hi : Lookup Γ i A) :
    ∀ ρ, RealizesContext Γ ρ → Realizes (.var i) A ρ := by
  induction hi with
  | here =>
    intro ρ hρ
    rcases hρ.2 with ⟨k, X, hX, hx⟩
    refine ⟨k, X, ?_, ?_⟩
    · rw [Term.weaken, eval_rename]
      exact hX
    · simpa only [eval_var] using hx
  | there hi ih =>
    intro ρ hρ
    rcases ih (Fin.tail ρ) hρ.1 with ⟨k, X, hX, hx⟩
    refine ⟨k, X, ?_, ?_⟩
    · rw [Term.weaken, eval_rename]
      exact hX
    · simpa only [eval_var, Fin.tail] using hx

/-- Exact source formation levels recover actual codes at that level. -/
theorem valid_code {n i : ℕ} {Γ : Context n} {A : Term n}
    (h : Valid Γ A (.univ i)) {ρ : Environment n 0} (hρ : RealizesContext Γ ρ) :
    ∃ X, Code i (eval A ρ) X := realizes_univ_iff.mp (h ρ hρ)

/-- Actual interpreted application, independent of any source formation derivation. -/
theorem realizes_app {n : ℕ} {f a A : Term n} {B : Term (n+1)} {ρ : Environment n 0}
    (hf : Realizes f (.pi A B) ρ) (ha : Realizes a A ρ) :
    Realizes (.app f a) (B.instantiate a) ρ := by
  rcases hf with ⟨i, T, hT, hf⟩
  rw [eval_pi] at hT
  rcases hT.pi_inv with ⟨X, Y, hA, hB, rfl⟩
  have ha' := realizes_mem hA ha
  refine ⟨i, Y (eval a ρ), ?_, ?_⟩
  · simpa only [eval_instantiate, instantiate_eval_lift] using hB (eval a ρ) ha'
  · simpa only [eval_app] using hf (eval a ρ) ha'

/-- A genuinely inhabited family of source formation codes gives actual uniform fibres. -/
theorem family_codes {n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n+1)}
    (hB : Valid (Γ.snoc A) B (.univ j)) {ρ : Environment n 0}
    {X : Set (Value 0)} (hρ : RealizesContext Γ ρ) (hA : Code i (eval A ρ) X) :
    ∃ Y : Value 0 → Set (Value 0), ∀ a ∈ X,
      Code j (instantiate (eval B (liftEnv ρ)) a) (Y a) := by
  classical
  have h : ∀ a : Value 0, ∃ Y : Set (Value 0), a ∈ X →
      Code j (instantiate (eval B (liftEnv ρ)) a) Y := by
    intro a
    by_cases ha : a ∈ X
    · rcases valid_code hB (context_cons hρ hA ha) with ⟨Y, hY⟩
      exact ⟨Y, fun _ => by simpa only [instantiate_eval_lift] using hY⟩
    · exact ⟨∅, fun h => False.elim (ha h)⟩
  choose Y hY using h
  exact ⟨Y, hY⟩


theorem valid_pi {n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n+1)}
    (hA : Valid Γ A (.univ i)) (hB : Valid (Γ.snoc A) B (.univ j)) :
    Valid Γ (.pi A B) (.univ (max i j)) := by
  intro ρ hρ
  rcases valid_code hA hρ with ⟨X, hX⟩
  rcases family_codes hB hρ hX with ⟨Y, hY⟩
  apply realizes_univ_iff.mpr
  exact ⟨FunctionSpace X Y, by
    rw [eval_pi]
    exact Code.pi (hX.lift (Nat.le_max_left i j))
      (fun a ha => (hY a ha).lift (Nat.le_max_right i j))⟩

theorem valid_sigma {n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n+1)}
    (hA : Valid Γ A (.univ i)) (hB : Valid (Γ.snoc A) B (.univ j)) :
    Valid Γ (.sigma A B) (.univ (max i j)) := by
  intro ρ hρ
  rcases valid_code hA hρ with ⟨X, hX⟩
  rcases family_codes hB hρ hX with ⟨Y, hY⟩
  apply realizes_univ_iff.mpr
  exact ⟨PairSpace X Y, by
    rw [eval_sigma]
    exact Code.sigma (hX.lift (Nat.le_max_left i j))
      (fun a ha => (hY a ha).lift (Nat.le_max_right i j))⟩

theorem valid_lam {n i j : ℕ} {Γ : Context n} {A : Term n} {B body : Term (n+1)}
    (hA : Valid Γ A (.univ i)) (hB : Valid (Γ.snoc A) B (.univ j))
    (ht : Valid (Γ.snoc A) body B) : Valid Γ (.lam A body) (.pi A B) := by
  intro ρ hρ
  rcases valid_code hA hρ with ⟨X, hX⟩
  rcases family_codes hB hρ hX with ⟨Y, hY⟩
  refine ⟨max i j, FunctionSpace X Y, ?_, ?_⟩
  · rw [eval_pi]
    exact Code.pi (hX.lift (Nat.le_max_left i j))
      (fun a ha => (hY a ha).lift (Nat.le_max_right i j))
  · intro a ha
    rw [eval_lam_app]
    apply realizes_mem (by simpa only [instantiate_eval_lift] using hY a ha)
    exact ht (Fin.cons a ρ) (context_cons hρ hX ha)

theorem valid_pair {n i j : ℕ} {Γ : Context n} {A a b : Term n} {B : Term (n+1)}
    (hA : Valid Γ A (.univ i)) (hB : Valid (Γ.snoc A) B (.univ j))
    (ha : Valid Γ a A) (hb : Valid Γ b (B.instantiate a)) :
    Valid Γ (.pair a b) (.sigma A B) := by
  intro ρ hρ
  rcases valid_code hA hρ with ⟨X, hX⟩
  rcases family_codes hB hρ hX with ⟨Y, hY⟩
  have ha' := realizes_mem hX (ha ρ hρ)
  have hb' : eval b ρ ∈ Y (eval a ρ) := realizes_mem
    (by simpa only [eval_instantiate, instantiate_eval_lift] using hY (eval a ρ) ha') (hb ρ hρ)
  refine ⟨max i j, PairSpace X Y, ?_, ?_⟩
  · rw [eval_sigma]
    exact Code.sigma (hX.lift (Nat.le_max_left i j))
      (fun a ha => (hY a ha).lift (Nat.le_max_right i j))
  · exact ⟨eval a ρ, ha', eval b ρ, hb', (eval_pair a b ρ)⟩

theorem valid_fst {n : ℕ} {Γ : Context n} {A p : Term n} {B : Term (n+1)}
    (hp : Valid Γ p (.sigma A B)) : Valid Γ (.fst p) A := by
  intro ρ hρ
  rcases hp ρ hρ with ⟨i, T, hT, hp⟩
  rw [eval_sigma] at hT
  rcases hT.sigma_inv with ⟨X, Y, hX, _, rfl⟩
  rcases hp with ⟨a, ha, b, _, hp⟩
  exact ⟨i, X, hX, by simpa only [eval_fst_realizer p ρ a b hp] using ha⟩

theorem valid_snd {n : ℕ} {Γ : Context n} {A p : Term n} {B : Term (n+1)}
    (hp : Valid Γ p (.sigma A B)) : Valid Γ (.snd p) (B.instantiate (.fst p)) := by
  intro ρ hρ
  rcases hp ρ hρ with ⟨i, T, hT, hp⟩
  rw [eval_sigma] at hT
  rcases hT.sigma_inv with ⟨X, Y, _, hY, rfl⟩
  rcases hp with ⟨a, ha, b, hb, hp⟩
  refine ⟨i, Y a, ?_, ?_⟩
  · simpa only [eval_instantiate, eval_fst_realizer p ρ a b hp, instantiate_eval_lift] using hY a ha
  · simpa only [eval_snd_realizer p ρ a b hp] using hb

theorem valid_id {n i : ℕ} {Γ : Context n} {A a b : Term n}
    (hA : Valid Γ A (.univ i)) (ha : Valid Γ a A) (hb : Valid Γ b A) :
    Valid Γ (.id A a b) (.univ i) := by
  intro ρ hρ
  rcases valid_code hA hρ with ⟨X, hX⟩
  apply realizes_univ_iff.mpr
  refine ⟨IdentitySpace (eval a ρ) (eval b ρ), ?_⟩
  rw [eval_id]
  exact Code.id hX (realizes_mem hX (ha ρ hρ)) (realizes_mem hX (hb ρ hρ))

theorem valid_refl {n i : ℕ} {Γ : Context n} {A a : Term n}
    (hA : Valid Γ A (.univ i)) (ha : Valid Γ a A) :
    Valid Γ (.refl a) (.id A a a) := by
  intro ρ hρ
  rcases valid_code hA hρ with ⟨X, hX⟩
  have ha' := realizes_mem hX (ha ρ hρ)
  refine ⟨i, IdentitySpace (eval a ρ) (eval a ρ), ?_, ?_⟩
  · rw [eval_id]
    exact Code.id hX ha' ha'
  · exact ⟨rfl, eval_refl a ρ⟩

theorem valid_conv {n : ℕ} {Γ : Context n} {t A B : Term n}
    (ht : Valid Γ t A) (hAB : Conversion A B) : Valid Γ t B := by
  intro ρ hρ
  rcases ht ρ hρ with ⟨i, X, hX, ht⟩
  have h := eval_conversion (LinearJ.ofConvertible ⟨hAB⟩) ρ
  exact ⟨i, X, h ▸ hX, ht⟩

theorem valid_cumulative {n i j : ℕ} {Γ : Context n} {A : Term n}
    (hA : Valid Γ A (.univ i)) (hij : i ≤ j) : Valid Γ A (.univ j) := by
  intro ρ hρ
  rcases valid_code hA hρ with ⟨X, hX⟩
  exact realizes_univ_iff.mpr ⟨X, hX.lift hij⟩


theorem valid_j {n : ℕ} {Γ : Context n} {A a d b p : Term n} {C : Term (n+2)}
    (hd : Valid Γ d (C.instantiate₂ a (.refl a)))
    (hp : Valid Γ p (.id A a b)) : Valid Γ (.j A a C d b p) (C.instantiate₂ b p) := by
  intro ρ hρ
  rcases hp ρ hρ with ⟨k, T, hT, hp⟩
  rw [eval_id] at hT
  rcases hT.id_inv with ⟨X, _, _, _, rfl⟩
  rcases hp with ⟨hab, hp⟩
  rcases hd ρ hρ with ⟨i, Y, hY, hd⟩
  refine ⟨i, Y, ?_, ?_⟩
  · rw [eval_instantiate₂, eval_refl] at hY
    rw [eval_instantiate₂, ← hab, hp]
    exact hY
  · simpa only [eval_j_refl A a d b p C ρ (eval a ρ) hp] using hd

theorem valid_succ {n : ℕ} {Γ : Context n} {t : Term n}
    (ht : Valid Γ t .nat) : Valid Γ (.succ t) .nat := by
  intro ρ hρ
  have ht' : eval t ρ ∈ Naturals := realizes_mem (Code.nat 0) (ht ρ hρ)
  rcases ht' with ⟨k, hk⟩
  refine ⟨0, Naturals, Code.nat 0, k+1, ?_⟩
  exact eval_succ_of_nat t ρ k hk

/-- Quotient membership at an actual dependent function code is closed under application. -/
theorem code_application {f a A : Value 0} {B : Value 1}
    (hf : ∃ i X, Code i (pi A B) X ∧ f ∈ X)
    (ha : ∃ i X, Code i A X ∧ a ∈ X) :
    ∃ i X, Code i (instantiate B a) X ∧ app f a ∈ X := by
  rcases hf with ⟨i, T, hT, hf⟩
  rcases hT.pi_inv with ⟨X, Y, hX, hY, rfl⟩
  rcases ha with ⟨j, Z, hZ, ha⟩
  rw [Code.functional hZ hX] at ha
  exact ⟨i, Y a, hY a ha, hf a ha⟩


theorem valid_natrec {n : ℕ} {Γ : Context n} {C : Term (n+1)} {z s t : Term n}
    (hz : Valid Γ z (C.instantiate .zero)) (hs : Valid Γ s C.natStepType)
    (ht : Valid Γ t .nat) : Valid Γ (.natrec C z s t) (C.instantiate t) := by
  intro ρ hρ
  let D : Term (n+2) := C.subst (Fin.cons (.succ (.var 1)) (fun i => .var i.succ.succ))
  let R : ℕ → Value 0 := fun k => ofTerm (.natrec
    (C.subst (Term.upSub (fun i => rep (ρ i))))
    (z.subst (fun i => rep (ρ i))) (s.subst (fun i => rep (ρ i))) (numeral k))
  have hR : ∀ k, ∃ i X, Code i (eval C (Fin.cons (ofTerm (numeral k)) ρ)) X ∧ R k ∈ X := by
    intro k
    induction k with
    | zero =>
      show ∃ i X, Code i (eval C (Fin.cons (ofTerm (numeral 0)) ρ)) X ∧ R 0 ∈ X
      rcases hz ρ hρ with ⟨i, X, hX, hz⟩
      have hZero : eval (.zero : Term n) ρ = ofTerm (numeral 0) := by
        simp only [eval, Term.subst, numeral]
      have hCode : Code i (eval C (Fin.cons (ofTerm (numeral 0)) ρ)) X := by
        simpa only [eval_instantiate, hZero] using hX
      have hMember : R 0 ∈ X := by simpa only [R, numeral, ofTerm_natrec_zero, eval] using hz
      exact ⟨i, X, hCode, hMember⟩
    | succ k ih =>
      show ∃ i X, Code i (eval C (Fin.cons (ofTerm (numeral (k+1))) ρ)) X ∧ R (k+1) ∈ X
      have hNat : eval (.nat : Term n) ρ = nat := by simp only [eval, Term.subst, nat]
      have hStep : ∃ i X,
          Code i (pi nat (eval (.pi C D) (liftEnv ρ))) X ∧ eval s ρ ∈ X := by
        simpa only [Realizes, Term.natStepType, eval_pi, D, hNat] using hs ρ hρ
      have hk : ∃ i X, Code i nat X ∧ ofTerm (numeral k) ∈ X :=
        ⟨0, Naturals, Code.nat 0, k, rfl⟩
      rcases code_application hStep hk with ⟨i, X, hX, hFirst⟩
      have hFirstCode : Code i (pi (eval C (Fin.cons (ofTerm (numeral k)) ρ))
          (eval D (liftEnv (Fin.cons (ofTerm (numeral k)) ρ)))) X := by
        rw [← eval_pi, ← instantiate_eval_lift]
        exact hX
      rcases code_application ⟨i, X, hFirstCode, hFirst⟩ ih with ⟨j, Y, hY, hr⟩
      have hNextCode : Code j (eval C (Fin.cons (ofTerm (numeral (k+1))) ρ)) Y := by
        simpa only [instantiate_eval_lift, D, eval_natStep_body, succ_rep_numeral] using hY
      have hMember : R (k+1) ∈ Y := by
        simpa only [R, numeral, ofTerm_natrec_succ, eval] using hr
      exact ⟨j, Y, hNextCode, hMember⟩
  have ht' : eval t ρ ∈ Naturals := realizes_mem (Code.nat 0) (ht ρ hρ)
  rcases ht' with ⟨k, hk⟩
  rcases hR k with ⟨i, X, hX, hr⟩
  refine ⟨i, X, ?_, ?_⟩
  · simpa only [eval_instantiate, hk] using hX
  · rw [eval_natrec_realizer C z s t ρ (numeral k) hk]
    exact hr

/-- Every unchanged original typing rule, including arbitrary raw conversion and exact J,
lands in the concrete cumulative quotient realizability model. -/
theorem realizes {n : ℕ} {Γ : Context n} {t A : Term n} (d : Derivation Γ t A) :
    Valid Γ t A := by
  induction d using Derivation.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc _ _ _ _ => trivial
  | univ _ i _ =>
    intro ρ _
    exact realizes_univ_iff.mpr ⟨{q | ∃ X, Code i q X}, Code.univ (Nat.lt_succ_self i)⟩
  | nat _ _ =>
    intro ρ _
    exact realizes_univ_iff.mpr ⟨Naturals, Code.nat 0⟩
  | empty _ _ =>
    intro ρ _
    exact realizes_univ_iff.mpr ⟨∅, Code.empty 0⟩
  | unit _ _ =>
    intro ρ _
    exact realizes_univ_iff.mpr ⟨Units, Code.unit 0⟩
  | var _ hi _ => exact lookup hi
  | pi _ _ ihA ihB => exact valid_pi ihA ihB
  | sigma _ _ ihA ihB => exact valid_sigma ihA ihB
  | lam _ _ _ ihA ihB iht => exact valid_lam ihA ihB iht
  | app _ _ ihf iha => exact fun ρ hρ => realizes_app (ihf ρ hρ) (iha ρ hρ)
  | pair _ _ _ _ ihA ihB iha ihb => exact valid_pair ihA ihB iha ihb
  | fst _ ihp => exact valid_fst ihp
  | snd _ ihp => exact valid_snd ihp
  | zero _ _ => exact fun _ _ => ⟨0, Naturals, Code.nat 0, 0, rfl⟩
  | succ _ iht => exact valid_succ iht
  | natrec _ _ _ _ _ ihz ihs iht => exact valid_natrec ihz ihs iht
  | star _ _ => exact fun _ _ => ⟨0, Units, Code.unit 0, rfl⟩
  | absurd _ _ _ ihe =>
    intro ρ hρ
    rcases ihe ρ hρ with ⟨i, X, hX, he⟩
    exact False.elim (hX.no_empty_realizer _ he)
  | id _ _ _ ihA iha ihb => exact valid_id ihA iha ihb
  | refl _ _ ihA iha => exact valid_refl ihA iha
  | j _ _ _ _ _ _ _ _ _ ihd _ ihp => exact valid_j ihd ihp
  | conv _ _ hAB iht _ => exact valid_conv iht hAB
  | cumulative _ hij ihA => exact valid_cumulative ihA hij

/-- Original closed Empty exclusion, with no restriction on source conversion nodes. -/
theorem no_closed_empty (t : Term 0) : ¬ Typing .nil t .empty := by
  rintro ⟨d⟩
  rcases realizes d Fin.elim0 trivial with ⟨i, X, hX, ht⟩
  exact hX.no_empty_realizer _ ht

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness
