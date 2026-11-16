module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.FiniteSoundness.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityFiniteSoundness

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

theorem univ_iff {cap n i : ℕ} {A : Term n} {ρ : Environment n 0} :
    RealizesAt cap A (.univ i) ρ ↔ i < cap ∧ ∃ X, Code i (eval A ρ) X := by
  constructor
  · rintro ⟨T, hT, hA⟩
    have h := hT.univ_inv
    rw [h.2] at hA
    exact ⟨h.1, hA⟩
  · rintro ⟨hi, X, hX⟩
    exact ⟨{q | ∃ Y, Code i q Y}, Code.univ hi, X, hX⟩

theorem mem {cap n k : ℕ} {t A : Term n} {ρ : Environment n 0} {X : Set (Value 0)}
    (hX : Code k (eval A ρ) X) (ht : RealizesAt cap t A ρ) : eval t ρ ∈ X := by
  rcases ht with ⟨Y, hY, ht⟩
  exact Code.functional hY hX ▸ ht

theorem context_cons {cap n : ℕ} {Γ : Context n} {A : Term n} {ρ : Environment n 0}
    {X : Set (Value 0)} {a : Value 0} (hρ : RealizesContextAt cap Γ ρ)
    (hA : Code cap (eval A ρ) X) (ha : a ∈ X) :
    RealizesContextAt cap (Γ.snoc A) (Fin.cons a ρ) := by
  simpa only [RealizesContextAt, Fin.tail_cons, Fin.cons_zero] using
    And.intro hρ (show ∃ Y, Code cap (eval A ρ) Y ∧ a ∈ Y from ⟨X, hA, ha⟩)

theorem lookup {cap n : ℕ} {Γ : Context n} {i : Fin n} {A : Term n} (hi : Lookup Γ i A) :
    ∀ ρ, RealizesContextAt cap Γ ρ → RealizesAt cap (.var i) A ρ := by
  induction hi with
  | here =>
    intro ρ hρ
    rcases hρ.2 with ⟨X, hX, hx⟩
    refine ⟨X, ?_, ?_⟩
    · rw [Term.weaken, eval_rename]
      exact hX
    · simpa only [eval_var] using hx
  | there hi ih =>
    intro ρ hρ
    rcases ih (Fin.tail ρ) hρ.1 with ⟨X, hX, hx⟩
    refine ⟨X, ?_, ?_⟩
    · rw [Term.weaken, eval_rename]
      exact hX
    · simpa only [eval_var, Fin.tail] using hx

theorem family_codes {cap n j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n+1)}
    (hB : ValidAt cap (Γ.snoc A) B (.univ j)) {ρ : Environment n 0}
    {X : Set (Value 0)} (hρ : RealizesContextAt cap Γ ρ) (hA : Code cap (eval A ρ) X) :
    ∃ Y : Value 0 → Set (Value 0), ∀ a ∈ X,
      Code j (instantiate (eval B (liftEnv ρ)) a) (Y a) := by
  classical
  have h : ∀ a : Value 0, ∃ Y : Set (Value 0), a ∈ X →
      Code j (instantiate (eval B (liftEnv ρ)) a) Y := by
    intro a
    by_cases ha : a ∈ X
    · rcases (univ_iff.mp (hB (Fin.cons a ρ) (context_cons hρ hA ha))).2 with ⟨Y, hY⟩
      exact ⟨Y, fun _ => by simpa only [instantiate_eval_lift] using hY⟩
    · exact ⟨∅, fun h => False.elim (ha h)⟩
  choose Y hY using h
  exact ⟨Y, hY⟩

theorem valid_pi {cap n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n+1)}
    (hi : i < cap) (hj : j < cap) (hA : ValidAt cap Γ A (.univ i))
    (hB : ValidAt cap (Γ.snoc A) B (.univ j)) : ValidAt cap Γ (.pi A B) (.univ (max i j)) := by
  intro ρ hρ
  rcases (univ_iff.mp (hA ρ hρ)).2 with ⟨X, hX⟩
  rcases family_codes hB hρ (hX.lift hi.le) with ⟨Y, hY⟩
  apply univ_iff.mpr
  refine ⟨max_lt hi hj, FunctionSpace X Y, ?_⟩
  rw [eval_pi]
  exact Code.pi (hX.lift (Nat.le_max_left i j))
    (fun a ha => (hY a ha).lift (Nat.le_max_right i j))

theorem valid_sigma {cap n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n+1)}
    (hi : i < cap) (hj : j < cap) (hA : ValidAt cap Γ A (.univ i))
    (hB : ValidAt cap (Γ.snoc A) B (.univ j)) : ValidAt cap Γ (.sigma A B) (.univ (max i j)) := by
  intro ρ hρ
  rcases (univ_iff.mp (hA ρ hρ)).2 with ⟨X, hX⟩
  rcases family_codes hB hρ (hX.lift hi.le) with ⟨Y, hY⟩
  apply univ_iff.mpr
  refine ⟨max_lt hi hj, PairSpace X Y, ?_⟩
  rw [eval_sigma]
  exact Code.sigma (hX.lift (Nat.le_max_left i j))
    (fun a ha => (hY a ha).lift (Nat.le_max_right i j))

theorem valid_lam {cap n i j : ℕ} {Γ : Context n} {A : Term n} {B body : Term (n+1)}
    (hi : i < cap) (hj : j < cap) (hA : ValidAt cap Γ A (.univ i))
    (hB : ValidAt cap (Γ.snoc A) B (.univ j)) (ht : ValidAt cap (Γ.snoc A) body B) :
    ValidAt cap Γ (.lam A body) (.pi A B) := by
  intro ρ hρ
  rcases (univ_iff.mp (hA ρ hρ)).2 with ⟨X, hX⟩
  have hXcap : Code cap (eval A ρ) X := hX.lift hi.le
  rcases family_codes hB hρ hXcap with ⟨Y, hY⟩
  refine ⟨FunctionSpace X Y, ?_, ?_⟩
  · rw [eval_pi]
    exact Code.pi hXcap (fun a ha => (hY a ha).lift hj.le)
  · intro a ha
    rw [eval_lam_app]
    apply mem (by simpa only [instantiate_eval_lift] using hY a ha)
    exact ht (Fin.cons a ρ) (context_cons hρ hXcap ha)

theorem valid_app {cap n : ℕ} {Γ : Context n} {f a A : Term n} {B : Term (n+1)}
    (hf : ValidAt cap Γ f (.pi A B)) (ha : ValidAt cap Γ a A) :
    ValidAt cap Γ (.app f a) (B.instantiate a) := by
  intro ρ hρ
  rcases hf ρ hρ with ⟨T, hT, hf⟩
  rw [eval_pi] at hT
  rcases hT.pi_inv with ⟨X, Y, hA, hB, rfl⟩
  have ha' := mem hA (ha ρ hρ)
  refine ⟨Y (eval a ρ), ?_, ?_⟩
  · simpa only [eval_instantiate, instantiate_eval_lift] using hB (eval a ρ) ha'
  · simpa only [eval_app] using hf (eval a ρ) ha'


theorem valid_pair {cap n i j : ℕ} {Γ : Context n} {A a b : Term n} {B : Term (n+1)}
    (hi : i < cap) (hj : j < cap) (hA : ValidAt cap Γ A (.univ i))
    (hB : ValidAt cap (Γ.snoc A) B (.univ j))
    (ha : ValidAt cap Γ a A) (hb : ValidAt cap Γ b (B.instantiate a)) :
    ValidAt cap Γ (.pair a b) (.sigma A B) := by
  intro ρ hρ
  rcases (univ_iff.mp (hA ρ hρ)).2 with ⟨X, hX⟩
  have hXcap : Code cap (eval A ρ) X := hX.lift hi.le
  rcases family_codes hB hρ hXcap with ⟨Y, hY⟩
  have ha' := mem hX (ha ρ hρ)
  have hb' : eval b ρ ∈ Y (eval a ρ) := mem
    (by simpa only [eval_instantiate, instantiate_eval_lift] using hY (eval a ρ) ha') (hb ρ hρ)
  refine ⟨PairSpace X Y, ?_, ?_⟩
  · rw [eval_sigma]
    exact Code.sigma hXcap (fun a ha => (hY a ha).lift hj.le)
  · exact ⟨eval a ρ, ha', eval b ρ, hb', eval_pair a b ρ⟩

theorem valid_fst {cap n : ℕ} {Γ : Context n} {A p : Term n} {B : Term (n+1)}
    (hp : ValidAt cap Γ p (.sigma A B)) : ValidAt cap Γ (.fst p) A := by
  intro ρ hρ
  rcases hp ρ hρ with ⟨T, hT, hp⟩
  rw [eval_sigma] at hT
  rcases hT.sigma_inv with ⟨X, Y, hX, _, rfl⟩
  rcases hp with ⟨a, ha, b, _, hp⟩
  exact ⟨X, hX, by simpa only [eval_fst_realizer p ρ a b hp] using ha⟩

theorem valid_snd {cap n : ℕ} {Γ : Context n} {A p : Term n} {B : Term (n+1)}
    (hp : ValidAt cap Γ p (.sigma A B)) : ValidAt cap Γ (.snd p) (B.instantiate (.fst p)) := by
  intro ρ hρ
  rcases hp ρ hρ with ⟨T, hT, hp⟩
  rw [eval_sigma] at hT
  rcases hT.sigma_inv with ⟨X, Y, _, hY, rfl⟩
  rcases hp with ⟨a, ha, b, hb, hp⟩
  refine ⟨Y a, ?_, ?_⟩
  · simpa only [eval_instantiate, eval_fst_realizer p ρ a b hp, instantiate_eval_lift] using hY a ha
  · simpa only [eval_snd_realizer p ρ a b hp] using hb

theorem valid_id {cap n i : ℕ} {Γ : Context n} {A a b : Term n}
    (hA : ValidAt cap Γ A (.univ i)) (ha : ValidAt cap Γ a A) (hb : ValidAt cap Γ b A) :
    ValidAt cap Γ (.id A a b) (.univ i) := by
  intro ρ hρ
  rcases univ_iff.mp (hA ρ hρ) with ⟨hi, X, hX⟩
  apply univ_iff.mpr
  refine ⟨hi, IdentitySpace (eval a ρ) (eval b ρ), ?_⟩
  rw [eval_id]
  exact Code.id hX (mem hX (ha ρ hρ)) (mem hX (hb ρ hρ))

theorem valid_refl {cap n i : ℕ} {Γ : Context n} {A a : Term n}
    (hA : ValidAt cap Γ A (.univ i)) (ha : ValidAt cap Γ a A) :
    ValidAt cap Γ (.refl a) (.id A a a) := by
  intro ρ hρ
  rcases univ_iff.mp (hA ρ hρ) with ⟨hi, X, hX⟩
  have hXcap : Code cap (eval A ρ) X := hX.lift hi.le
  have ha' := mem hXcap (ha ρ hρ)
  refine ⟨IdentitySpace (eval a ρ) (eval a ρ), ?_, ?_⟩
  · rw [eval_id]
    exact Code.id hXcap ha' ha'
  · exact ⟨rfl, eval_refl a ρ⟩

theorem valid_conv {cap n : ℕ} {Γ : Context n} {t A B : Term n}
    (ht : ValidAt cap Γ t A) (hAB : Conversion A B) : ValidAt cap Γ t B := by
  intro ρ hρ
  rcases ht ρ hρ with ⟨X, hX, ht⟩
  have h := eval_conversion (LinearJ.ofConvertible ⟨hAB⟩) ρ
  exact ⟨X, h ▸ hX, ht⟩

theorem valid_cumulative {cap n i j : ℕ} {Γ : Context n} {A : Term n}
    (hj : j < cap) (hA : ValidAt cap Γ A (.univ i)) (hij : i ≤ j) :
    ValidAt cap Γ A (.univ j) := by
  intro ρ hρ
  rcases (univ_iff.mp (hA ρ hρ)).2 with ⟨X, hX⟩
  exact univ_iff.mpr ⟨hj, X, hX.lift hij⟩

theorem valid_j {cap n : ℕ} {Γ : Context n} {A a d b p : Term n} {C : Term (n+2)}
    (hd : ValidAt cap Γ d (C.instantiate₂ a (.refl a)))
    (hp : ValidAt cap Γ p (.id A a b)) : ValidAt cap Γ (.j A a C d b p) (C.instantiate₂ b p) := by
  intro ρ hρ
  rcases hp ρ hρ with ⟨T, hT, hp⟩
  rw [eval_id] at hT
  rcases hT.id_inv with ⟨X, _, _, _, rfl⟩
  rcases hp with ⟨hab, hp⟩
  rcases hd ρ hρ with ⟨Y, hY, hd⟩
  refine ⟨Y, ?_, ?_⟩
  · rw [eval_instantiate₂, eval_refl] at hY
    rw [eval_instantiate₂, ← hab, hp]
    exact hY
  · simpa only [eval_j_refl A a d b p C ρ (eval a ρ) hp] using hd

theorem valid_succ {cap n : ℕ} {Γ : Context n} {t : Term n}
    (ht : ValidAt cap Γ t .nat) : ValidAt cap Γ (.succ t) .nat := by
  intro ρ hρ
  have ht' : eval t ρ ∈ Naturals := mem (Code.nat cap) (ht ρ hρ)
  rcases ht' with ⟨k, hk⟩
  exact ⟨Naturals, Code.nat cap, k+1, eval_succ_of_nat t ρ k hk⟩

theorem code_application {cap : ℕ} {f a A : Value 0} {B : Value 1}
    (hf : ∃ X, Code cap (pi A B) X ∧ f ∈ X)
    (ha : ∃ X, Code cap A X ∧ a ∈ X) :
    ∃ X, Code cap (instantiate B a) X ∧ app f a ∈ X := by
  rcases hf with ⟨T, hT, hf⟩
  rcases hT.pi_inv with ⟨X, Y, hX, hY, rfl⟩
  rcases ha with ⟨Z, hZ, ha⟩
  rw [Code.functional hZ hX] at ha
  exact ⟨Y a, hY a ha, hf a ha⟩

theorem valid_natrec {cap n : ℕ} {Γ : Context n} {C : Term (n+1)} {z s t : Term n}
    (hz : ValidAt cap Γ z (C.instantiate .zero)) (hs : ValidAt cap Γ s C.natStepType)
    (ht : ValidAt cap Γ t .nat) : ValidAt cap Γ (.natrec C z s t) (C.instantiate t) := by
  intro ρ hρ
  let D : Term (n+2) := C.subst (Fin.cons (.succ (.var 1)) (fun i => .var i.succ.succ))
  let R : ℕ → Value 0 := fun k => ofTerm (.natrec
    (C.subst (Term.upSub (fun i => rep (ρ i))))
    (z.subst (fun i => rep (ρ i))) (s.subst (fun i => rep (ρ i))) (numeral k))
  have hR : ∀ k, ∃ X, Code cap (eval C (Fin.cons (ofTerm (numeral k)) ρ)) X ∧ R k ∈ X := by
    intro k
    induction k with
    | zero =>
      show ∃ X, Code cap (eval C (Fin.cons (ofTerm (numeral 0)) ρ)) X ∧ R 0 ∈ X
      rcases hz ρ hρ with ⟨X, hX, hz⟩
      have hZero : eval (.zero : Term n) ρ = ofTerm (numeral 0) := by
        simp only [eval, Term.subst, numeral]
      have hCode : Code cap (eval C (Fin.cons (ofTerm (numeral 0)) ρ)) X := by
        simpa only [eval_instantiate, hZero] using hX
      have hMember : R 0 ∈ X := by simpa only [R, numeral, ofTerm_natrec_zero, eval] using hz
      exact ⟨X, hCode, hMember⟩
    | succ k ih =>
      show ∃ X, Code cap (eval C (Fin.cons (ofTerm (numeral (k+1))) ρ)) X ∧ R (k+1) ∈ X
      have hNat : eval (.nat : Term n) ρ = nat := by simp only [eval, Term.subst, nat]
      have hStep : ∃ X,
          Code cap (pi nat (eval (.pi C D) (liftEnv ρ))) X ∧ eval s ρ ∈ X := by
        simpa only [RealizesAt, Term.natStepType, eval_pi, D, hNat] using hs ρ hρ
      have hk : ∃ X, Code cap nat X ∧ ofTerm (numeral k) ∈ X :=
        ⟨Naturals, Code.nat cap, k, rfl⟩
      rcases code_application hStep hk with ⟨X, hX, hFirst⟩
      have hFirstCode : Code cap (pi (eval C (Fin.cons (ofTerm (numeral k)) ρ))
          (eval D (liftEnv (Fin.cons (ofTerm (numeral k)) ρ)))) X := by
        rw [← eval_pi, ← instantiate_eval_lift]
        exact hX
      rcases code_application ⟨X, hFirstCode, hFirst⟩ ih with ⟨Y, hY, hr⟩
      have hNextCode : Code cap (eval C (Fin.cons (ofTerm (numeral (k+1))) ρ)) Y := by
        simpa only [instantiate_eval_lift, D, eval_natStep_body, succ_rep_numeral] using hY
      have hMember : R (k+1) ∈ Y := by
        simpa only [R, numeral, ofTerm_natrec_succ, eval] using hr
      exact ⟨Y, hNextCode, hMember⟩
  have ht' : eval t ρ ∈ Naturals := mem (Code.nat cap) (ht ρ hρ)
  rcases ht' with ⟨k, hk⟩
  rcases hR k with ⟨X, hX, hr⟩
  refine ⟨X, ?_, ?_⟩
  · simpa only [eval_instantiate, hk] using hX
  · rw [eval_natrec_realizer C z s t ρ (numeral k) hk]
    exact hr


/-- Universe carriers in an actual source proof stay strictly within its whole-tree cap. -/
theorem level_lt {H : Set ScopedTyping} {n i cap : ℕ} {Γ : Context n} {t : Term n}
    (d : DerivationH H Γ t (.univ i)) (hBudget : d.universeBudget ≤ cap) : i < cap := by
  have hJudgment := d.judgment_le_budget.trans hBudget
  have hScope : max Γ.universeBound (max t.universeBound (Term.univ i : Term n).universeBound) ≤ cap := by
    simpa only [ScopedTyping.universeBound] using hJudgment
  have hi : (Term.univ i : Term n).universeBound ≤ cap :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hScope)
  exact Nat.lt_of_succ_le (by simpa only [Term.universeBound] using hi)

/-- Every bounded original rule with actual typing hypotheses is sound at the concrete cap. -/
theorem realizes {H : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH H Γ t A) : ∀ cap, d.universeBudget ≤ cap →
    (∀ q ∈ H, ValidAt cap q.Γ q.term q.carrier) → ValidAt cap Γ t A := by
  induction d using DerivationH.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc _ _ _ _ => trivial
  | hyp hq => exact fun _ _ hH => hH _ hq
  | univ hΓ i _ =>
    intro cap hBudget _ ρ _
    exact univ_iff.mpr ⟨level_lt (.univ hΓ i) hBudget,
      {q | ∃ X, Code i q X}, Code.univ (Nat.lt_succ_self i)⟩
  | nat hΓ _ =>
    intro cap hBudget _ ρ _
    exact univ_iff.mpr ⟨level_lt (.nat hΓ) hBudget, Naturals, Code.nat 0⟩
  | empty hΓ _ =>
    intro cap hBudget _ ρ _
    exact univ_iff.mpr ⟨level_lt (.empty hΓ) hBudget, ∅, Code.empty 0⟩
  | unit hΓ _ =>
    intro cap hBudget _ ρ _
    exact univ_iff.mpr ⟨level_lt (.unit hΓ) hBudget, Units, Code.unit 0⟩
  | var _ hi _ => exact fun _ _ _ => lookup hi
  | zero _ _ => exact fun cap _ _ _ _ => ⟨Naturals, Code.nat cap, 0, rfl⟩
  | star _ _ => exact fun cap _ _ _ _ => ⟨Units, Code.unit cap, rfl⟩
  | pi sourceA sourceB ihA ihB =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : (max sourceA.universeBudget sourceB.universeBudget) ≤ cap := (max_le_iff.mp hBudget).2
    rcases max_le_iff.mp bChildren with ⟨bA, bB⟩
    exact valid_pi (level_lt sourceA bA) (level_lt sourceB bB) (ihA cap bA hH) (ihB cap bB hH)
  | sigma sourceA sourceB ihA ihB =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : (max sourceA.universeBudget sourceB.universeBudget) ≤ cap := (max_le_iff.mp hBudget).2
    rcases max_le_iff.mp bChildren with ⟨bA, bB⟩
    exact valid_sigma (level_lt sourceA bA) (level_lt sourceB bB) (ihA cap bA hH) (ihB cap bB hH)
  | lam sourceA sourceB sourcet ihA ihB iht =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : (max sourceA.universeBudget (max sourceB.universeBudget sourcet.universeBudget)) ≤ cap := (max_le_iff.mp hBudget).2
    rcases max_le_iff.mp bChildren with ⟨bA, bGroup4R⟩
    rcases max_le_iff.mp bGroup4R with ⟨bB, bt⟩
    exact valid_lam (level_lt sourceA bA) (level_lt sourceB bB) (ihA cap bA hH) (ihB cap bB hH) (iht cap bt hH)
  | app sourcef sourcea ihf iha =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : (max sourcef.universeBudget sourcea.universeBudget) ≤ cap := (max_le_iff.mp hBudget).2
    rcases max_le_iff.mp bChildren with ⟨bf, ba⟩
    exact valid_app (ihf cap bf hH) (iha cap ba hH)
  | pair sourceA sourceB sourcea sourceb ihA ihB iha ihb =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : (max (max sourceA.universeBudget sourceB.universeBudget) (max sourcea.universeBudget sourceb.universeBudget)) ≤ cap := (max_le_iff.mp hBudget).2
    rcases max_le_iff.mp bChildren with ⟨bGroup4L, bGroup4R⟩
    rcases max_le_iff.mp bGroup4L with ⟨bA, bB⟩
    rcases max_le_iff.mp bGroup4R with ⟨ba, bb⟩
    exact valid_pair (level_lt sourceA bA) (level_lt sourceB bB) (ihA cap bA hH) (ihB cap bB hH) (iha cap ba hH) (ihb cap bb hH)
  | fst sourcep ihp =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : sourcep.universeBudget ≤ cap := (max_le_iff.mp hBudget).2
    exact valid_fst (ihp cap bChildren hH)
  | snd sourcep ihp =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : sourcep.universeBudget ≤ cap := (max_le_iff.mp hBudget).2
    exact valid_snd (ihp cap bChildren hH)
  | succ sourcet iht =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : sourcet.universeBudget ≤ cap := (max_le_iff.mp hBudget).2
    exact valid_succ (iht cap bChildren hH)
  | natrec sourceC sourcez sources sourcet _ ihz ihs iht =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : (max (max sourceC.universeBudget sourcez.universeBudget) (max sources.universeBudget sourcet.universeBudget)) ≤ cap := (max_le_iff.mp hBudget).2
    rcases max_le_iff.mp bChildren with ⟨bGroup4L, bGroup4R⟩
    rcases max_le_iff.mp bGroup4L with ⟨bC, bz⟩
    rcases max_le_iff.mp bGroup4R with ⟨bs, bt⟩
    exact valid_natrec (ihz cap bz hH) (ihs cap bs hH) (iht cap bt hH)
  | id sourceA sourcea sourceb ihA iha ihb =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : (max sourceA.universeBudget (max sourcea.universeBudget sourceb.universeBudget)) ≤ cap := (max_le_iff.mp hBudget).2
    rcases max_le_iff.mp bChildren with ⟨bA, bGroup4R⟩
    rcases max_le_iff.mp bGroup4R with ⟨ba, bb⟩
    exact valid_id (ihA cap bA hH) (iha cap ba hH) (ihb cap bb hH)
  | refl sourceA sourcea ihA iha =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : (max sourceA.universeBudget sourcea.universeBudget) ≤ cap := (max_le_iff.mp hBudget).2
    rcases max_le_iff.mp bChildren with ⟨bA, ba⟩
    exact valid_refl (ihA cap bA hH) (iha cap ba hH)
  | @j n i j Γ A a d b p C sourceA sourcea sourceC sourced sourceb sourcep _ _ _ ihd _ ihp =>
    show ∀ cap, (DerivationH.j sourceA sourcea sourceC sourced sourceb sourcep).universeBudget ≤ cap →
      (∀ q ∈ H, ValidAt cap q.Γ q.term q.carrier) →
      ValidAt cap Γ (.j A a C d b p) (C.instantiate₂ b p)
    intro cap hBudget hH
    have bChildren : (max (max sourceA.universeBudget sourcea.universeBudget) (max (max sourceC.universeBudget sourced.universeBudget) (max sourceb.universeBudget sourcep.universeBudget))) ≤ cap := (max_le_iff.mp hBudget).2
    rcases max_le_iff.mp bChildren with ⟨bGroup4L, bGroup4R⟩
    rcases max_le_iff.mp bGroup4L with ⟨bA, ba⟩
    rcases max_le_iff.mp bGroup4R with ⟨bGroup6L, bGroup6R⟩
    rcases max_le_iff.mp bGroup6L with ⟨bC, bd⟩
    rcases max_le_iff.mp bGroup6R with ⟨bb, bp⟩
    exact valid_j (ihd cap bd hH) (ihp cap bp hH)
  | conv sourcet sourceB sourceconversion iht _ =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : (max sourcet.universeBudget (max sourceB.universeBudget sourceconversion.universeBudget)) ≤ cap := (max_le_iff.mp hBudget).2
    rcases max_le_iff.mp bChildren with ⟨bt, bGroup4R⟩
    rcases max_le_iff.mp bGroup4R with ⟨bB, bconversion⟩
    exact valid_conv (iht cap bt hH) sourceconversion
  | cumulative sourceA hij ihA =>
    intro cap hBudget hH
    show ValidAt cap _ _ _
    have bChildren : sourceA.universeBudget ≤ cap := (max_le_iff.mp hBudget).2
    exact valid_cumulative (level_lt (.cumulative sourceA hij) hBudget) (ihA cap bChildren hH) hij
  | absurd _ sourceE _ ihe =>
    intro cap hBudget hH ρ hρ
    have bE : sourceE.universeBudget ≤ cap :=
      (Nat.le_max_right _ _).trans ((max_le_iff.mp hBudget).2)
    rcases ihe cap bE hH ρ hρ with ⟨X, hX, he⟩
    exact False.elim (hX.no_empty_realizer _ he)

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityFiniteSoundness
