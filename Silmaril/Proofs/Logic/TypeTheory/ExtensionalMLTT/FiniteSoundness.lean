module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Soundness.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FiniteSoundness

open Silmaril.Logic.TypeTheory.ExtensionalMLTT Silmaril.Logic.SetTheory ZFSet Silmaril.Logic.SetTheory

universe u

private theorem snoc_empty (z : ZFSet.{u}) :
    (Fin.snoc (Fin.elim0 : Fin 0 → ZFSet.{u}) z : Fin 1 → ZFSet.{u}) =
      (Fin.cons z Fin.elim0 : Fin 1 → ZFSet.{u}) := by
  funext i
  have hi : i = 0 := by
    apply Fin.ext
    have hi : i.val < 1 := i.isLt
    omega
  subst i
  rfl

private theorem tower_mono {levels i j : ℕ} (T : FiniteTower.{u} levels)
    (hij : i ≤ j) (hj : j < levels) : T.U i ⊆ T.U j := by
  induction hij with
  | refl => exact fun _ h => h
  | @step j hij ih =>
    have hj' : j < levels := Nat.lt_of_succ_lt hj
    exact fun _ hx => (T.isGrothendieck (j + 1) hj).isTransitive
      (T.U j) (T.mem_succ j hj) (ih hj' hx)

noncomputable section

/-- Equality and typing at one environment, including environments under a binder. -/
private abbrev RelatedAt (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (A a b : ETm k) : Prop :=
  a.denoteIn U ρ β = b.denoteIn U ρ β ∧ a.denoteIn U ρ β ∈ A.denoteIn U ρ β

/-- Every inference rule preserves validity in a hierarchy of set universes. -/
theorem sound {levels : ℕ} (T : FiniteTower.{u} levels) {H : Set EJdg}
    (hH : ∀ j ∈ H, EJdg.ValidIn T.U j) {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b) : EJdg.ValidIn T.U ⟨Γ, A, a, b⟩ := by
  induction h with
  | hyp hj => exact hH _ hj
  | nil_ok =>
    intro ρ hΓ
    exact ⟨rfl, by simp [ETm.denoteIn]⟩
  | cons_ok hn hΓ hx hA ihΓ ihA =>
    intro ρ hΓ
    exact ⟨rfl, by simp [ETm.denoteIn]⟩
  | var hΓ hx ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, hx.satIn T.U ρ hΓ⟩
  | univ hn hΓ ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, T.mem_succ _ hn⟩
  | empty hn hΓ ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, (T.isGrothendieck _ hn).empty_mem⟩
  | unit hn hΓ ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, (T.isGrothendieck _ hn).singleton_mem (T.isGrothendieck _ hn).empty_mem⟩
  | nats hn hΓ ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, (T.isGrothendieck _ hn).omega_mem⟩
  | zero hΓ ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, omega_zero⟩
  | @succ Γ m m' h ih =>
    intro ρ hΓ
    have hv : RelatedAt T.U ρ Fin.elim0 .nats m m' := ih ρ hΓ
    exact ⟨congrArg (fun x => insert x x) hv.1, omega_succ hv.2⟩
  | @pi Γ n hn A A' B B' L hA hB ihA ihB =>
    show EJdg.ValidIn T.U ⟨Γ, .univ n, .pi A B, .pi A' B'⟩
    intro ρ hΓ
    have ha : RelatedAt T.U ρ Fin.elim0 (.univ n) A A' := ihA ρ hΓ
    have hb : ∀ z ∈ A.denoteIn T.U ρ Fin.elim0,
        RelatedAt T.U ρ (Fin.cons z Fin.elim0) (.univ n) B B' :=
      binder_validIn T.U (Γ := Γ) (A := A) (C := .univ n) (a := B) (b := B') (L := L)
      (by intro x hx; simpa only [ETm.open] using ihB x hx) ρ hΓ
    constructor
    · change SetSem.pi _ _ = SetSem.pi _ _
      rw [ha.1]
      apply SetSem.pi_congr
      intro z hz
      exact (hb z (ha.1.symm ▸ hz)).1
    · exact SetSem.pi_mem (T.isGrothendieck n hn) ha.2 (fun z hz => (hb z hz).2)
  | @sigma Γ n hn A A' B B' L hA hB ihA ihB =>
    show EJdg.ValidIn T.U ⟨Γ, .univ n, .sigma A B, .sigma A' B'⟩
    intro ρ hΓ
    have ha : RelatedAt T.U ρ Fin.elim0 (.univ n) A A' := ihA ρ hΓ
    have hb : ∀ z ∈ A.denoteIn T.U ρ Fin.elim0,
        RelatedAt T.U ρ (Fin.cons z Fin.elim0) (.univ n) B B' :=
      binder_validIn T.U (Γ := Γ) (A := A) (C := .univ n) (a := B) (b := B') (L := L)
      (by intro x hx; simpa only [ETm.open] using ihB x hx) ρ hΓ
    constructor
    · change SetSem.sigma _ _ = SetSem.sigma _ _
      rw [ha.1]
      apply SetSem.sigma_congr
      intro z hz
      exact (hb z (ha.1.symm ▸ hz)).1
    · exact SetSem.sigma_mem (T.isGrothendieck n hn) ha.2 (fun z hz => (hb z hz).2)
  | @id Γ n hn A A' a a' b b' hA ha hb ihA iha ihb =>
    intro ρ hΓ
    have hvA : RelatedAt T.U ρ Fin.elim0 A a a' := iha ρ hΓ
    have hvB : RelatedAt T.U ρ Fin.elim0 A b b' := ihb ρ hΓ
    constructor
    · change SetSem.truth _ = SetSem.truth _
      rw [hvA.1, hvB.1]
    · exact SetSem.truth_mem (T.isGrothendieck n hn) _
  | @abs Γ n hn A A' B b b' L hA hB hb ihA ihB ihb =>
    show EJdg.ValidIn T.U ⟨Γ, .pi A B, .abs A b, .abs A' b'⟩
    intro ρ hΓ
    have ha : RelatedAt T.U ρ Fin.elim0 (.univ n) A A' := ihA ρ hΓ
    have hvb : ∀ z ∈ A.denoteIn T.U ρ Fin.elim0,
        RelatedAt T.U ρ (Fin.cons z Fin.elim0) B b b' :=
      binder_validIn T.U (Γ := Γ) (A := A) (C := B) (a := b) (b := b') (L := L) ihb ρ hΓ
    constructor
    · change SetSem.lam _ _ = SetSem.lam _ _
      rw [ha.1]
      apply SetSem.lam_congr
      intro z hz
      exact (hvb z (ha.1.symm ▸ hz)).1
    · exact SetSem.lam_mem_pi (fun z hz => (hvb z hz).2)
  | @app Γ n hn A f f' a a' B L hA hB hf ha ihA ihB ihf iha =>
    intro ρ hΓ
    have hvf : RelatedAt T.U ρ Fin.elim0 (.pi A B) f f' := ihf ρ hΓ
    have hva : RelatedAt T.U ρ Fin.elim0 A a a' := iha ρ hΓ
    constructor
    · exact congrArg₂ SetSem.app hvf.1 hva.1
    · rw [ETm.denoteIn_lst0]
      exact SetSem.app_mem_of_mem_pi hvf.2 hva.2
  | @pair Γ n hn A a a' b b' B L hA hB ha hb ihA ihB iha ihb =>
    intro ρ hΓ
    have hva : RelatedAt T.U ρ Fin.elim0 A a a' := iha ρ hΓ
    have hvb : RelatedAt T.U ρ Fin.elim0 (B.lst a) b b' := ihb ρ hΓ
    constructor
    · exact congrArg₂ SetSem.pair hva.1 hvb.1
    · apply SetSem.pair_mem_sigma.2
      exact ⟨hva.2, by simpa only [ETm.denoteIn_lst0] using hvb.2⟩
  | @fst Γ n hn A p p' B L hA hB hp ihA ihB ihp =>
    intro ρ hΓ
    have hvp : RelatedAt T.U ρ Fin.elim0 (.sigma A B) p p' := ihp ρ hΓ
    exact ⟨congrArg SetSem.fst hvp.1, SetSem.fst_mem_of_mem_sigma hvp.2⟩
  | @snd Γ n hn A p p' B L hA hB hp ihA ihB ihp =>
    intro ρ hΓ
    have hvp : RelatedAt T.U ρ Fin.elim0 (.sigma A B) p p' := ihp ρ hΓ
    constructor
    · exact congrArg SetSem.snd hvp.1
    · rw [ETm.denoteIn_lst0]
      exact SetSem.snd_mem_of_mem_sigma hvp.2
  | @natrec Γ n hn C C' s s' z z' m m' L hC hz hs hm ihC ihz ihs ihm =>
    show EJdg.ValidIn T.U ⟨Γ, C.lst m, .natrec C s z m, .natrec C' s' z' m'⟩
    intro ρ hΓ
    have hvz : RelatedAt T.U ρ Fin.elim0 (C.lst .zero) z z' := ihz ρ hΓ
    have hvm : RelatedAt T.U ρ Fin.elim0 .nats m m' := ihm ρ hΓ
    have hvstep : ∀ m ∈ omega,
        s.denoteIn T.U ρ (Fin.cons m Fin.elim0) = s'.denoteIn T.U ρ (Fin.cons m Fin.elim0) ∧
        s.denoteIn T.U ρ (Fin.cons m Fin.elim0) ∈
          SetSem.pi (C.denoteIn T.U ρ (Fin.cons m Fin.elim0))
            (fun _ => C.denoteIn T.U ρ (Fin.cons (insert m m) Fin.elim0)) :=
      natstep_validIn T.U ihs ρ hΓ
    let B : ZFSet.{u} → ZFSet.{u} := fun a => C.denoteIn T.U ρ (Fin.cons a Fin.elim0)
    let step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
      fun a r => SetSem.app (s.denoteIn T.U ρ (Fin.cons a Fin.elim0)) r
    have hzB : z.denoteIn T.U ρ Fin.elim0 ∈ B ∅ := by
      simpa only [ETm.denoteIn_lst0, ETm.denoteIn, B] using hvz.2
    have hsB : ∀ a ∈ omega, ∀ r ∈ B a, step a r ∈ B (insert a a) := by
      intro a ha r hr
      exact SetSem.app_mem_of_mem_pi (hvstep a ha).2 hr
    constructor
    · change SetSem.natrec _ _ _ = SetSem.natrec _ _ _
      rw [← hvm.1]
      apply SetSem.natrec_congr (B := B) hvz.1 hzB hsB _ hvm.2
      intro a ha r hr
      exact congrArg (fun f => SetSem.app f r) (hvstep a ha).1
    · rw [ETm.denoteIn_lst0]
      exact SetSem.natrec_mem hzB hsB hvm.2
  | refl ha iha =>
    intro ρ hΓ
    exact ⟨rfl, SetSem.mem_truth.2 ⟨rfl, rfl⟩⟩
  | absurd hn hC he ihC ihe =>
    intro ρ hΓ
    exact (notMem_empty _ (ihe ρ hΓ).2).elim
  | @beta_app Γ n hn A a B b L hA hB hb ha ihA ihB ihb iha =>
    show EJdg.ValidIn T.U ⟨Γ, B.lst a, .app (.abs A b) a, b.lst a⟩
    intro ρ hΓ
    have hva : RelatedAt T.U ρ Fin.elim0 A a a := iha ρ hΓ
    have hvb : RelatedAt T.U ρ (Fin.cons (a.denoteIn T.U ρ Fin.elim0) Fin.elim0) B b b :=
      binder_validIn T.U (Γ := Γ) (A := A) (C := B) (a := b) (b := b) (L := L) ihb ρ hΓ _ hva.2
    constructor
    · simpa only [ETm.denoteIn, ETm.denoteIn_lst0] using
        SetSem.app_lam (fun z => b.denoteIn T.U ρ (Fin.cons z Fin.elim0)) hva.2
    · rw [ETm.denoteIn_lst0]
      change SetSem.app (SetSem.lam _ _) _ ∈ _
      rw [SetSem.app_lam _ hva.2]
      exact hvb.2
  | beta_fst hn hA hB ha hb ihA ihB iha ihb =>
    intro ρ hΓ
    constructor
    · exact SetSem.fst_pair _ _
    · simpa only [ETm.denoteIn, SetSem.fst_pair] using (iha ρ hΓ).2
  | beta_snd hn hA hB ha hb ihA ihB iha ihb =>
    intro ρ hΓ
    constructor
    · exact SetSem.snd_pair _ _
    · simpa only [ETm.denoteIn, SetSem.snd_pair] using (ihb ρ hΓ).2
  | beta_natrec_zero hn hC hz hs ihC ihz ihs =>
    intro ρ hΓ
    constructor
    · exact SetSem.natrec_zero _ _
    · simpa only [ETm.denoteIn, SetSem.natrec_zero] using (ihz ρ hΓ).2
  | @beta_natrec_succ Γ n hn C s z m L hC hz hs hm ihC ihz ihs ihm =>
    show EJdg.ValidIn T.U ⟨Γ, C.lst (.succ m), .natrec C s z (.succ m), .app (s.lst m) (.natrec C s z m)⟩
    intro ρ hΓ
    have hvz : RelatedAt T.U ρ Fin.elim0 (C.lst .zero) z z := ihz ρ hΓ
    have hvm : RelatedAt T.U ρ Fin.elim0 .nats m m := ihm ρ hΓ
    have hvstep : ∀ m ∈ omega,
        s.denoteIn T.U ρ (Fin.cons m Fin.elim0) = s.denoteIn T.U ρ (Fin.cons m Fin.elim0) ∧
        s.denoteIn T.U ρ (Fin.cons m Fin.elim0) ∈
          SetSem.pi (C.denoteIn T.U ρ (Fin.cons m Fin.elim0))
            (fun _ => C.denoteIn T.U ρ (Fin.cons (insert m m) Fin.elim0)) :=
      natstep_validIn T.U ihs ρ hΓ
    let B : ZFSet.{u} → ZFSet.{u} := fun a => C.denoteIn T.U ρ (Fin.cons a Fin.elim0)
    let step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
      fun a r => SetSem.app (s.denoteIn T.U ρ (Fin.cons a Fin.elim0)) r
    have hzB : z.denoteIn T.U ρ Fin.elim0 ∈ B ∅ := by
      simpa only [ETm.denoteIn_lst0, ETm.denoteIn, B] using hvz.2
    have hsB : ∀ a ∈ omega, ∀ r ∈ B a, step a r ∈ B (insert a a) := by
      intro a ha r hr
      exact SetSem.app_mem_of_mem_pi (hvstep a ha).2 hr
    constructor
    · simpa only [ETm.denoteIn, ETm.denoteIn_lst0] using
        SetSem.natrec_succ (z.denoteIn T.U ρ Fin.elim0) step hvm.2
    · rw [ETm.denoteIn_lst0]
      exact SetSem.natrec_mem hzB hsB (omega_succ hvm.2)
  | reflect ha hb hp iha ihb ihp =>
    intro ρ hΓ
    exact ⟨(SetSem.mem_truth.1 (ihp ρ hΓ).2).1, (iha ρ hΓ).2⟩
  | id_uip ha hb hp iha ihb ihp =>
    intro ρ hΓ
    exact ⟨(SetSem.mem_truth.1 (ihp ρ hΓ).2).2, (ihp ρ hΓ).2⟩
  | unit_ext ha iha =>
    intro ρ hΓ
    exact ⟨SetSem.mem_tt.1 (iha ρ hΓ).2, (iha ρ hΓ).2⟩
  | @pi_ext Γ n hn A f g B L hA hB hf hg hfg ihA ihB ihf ihg ihfg =>
    show EJdg.ValidIn T.U ⟨Γ, .pi A B, f, g⟩
    intro ρ hΓ
    have hvf : RelatedAt T.U ρ Fin.elim0 (.pi A B) f f := ihf ρ hΓ
    have hvg : RelatedAt T.U ρ Fin.elim0 (.pi A B) g g := ihg ρ hΓ
    constructor
    · show f.denoteIn T.U ρ Fin.elim0 = g.denoteIn T.U ρ Fin.elim0
      apply SetSem.pi_ext hvf.2 hvg.2
      intro z hz
      have hb :
          (ETm.app (f.castLE (by omega)) (.bv 0)).denoteIn T.U ρ (Fin.cons z Fin.elim0) =
            (ETm.app (g.castLE (by omega)) (.bv 0)).denoteIn T.U ρ (Fin.cons z Fin.elim0) ∧
          (ETm.app (f.castLE (by omega)) (.bv 0)).denoteIn T.U ρ (Fin.cons z Fin.elim0) ∈
            B.denoteIn T.U ρ (Fin.cons z Fin.elim0) :=
        binder_validIn T.U (Γ := Γ) (A := A) (C := B) (L := L)
        (a := .app (f.castLE (by omega)) (.bv 0))
        (b := .app (g.castLE (by omega)) (.bv 0))
        (by
          intro x hx ρ' hΓ'
          have hv := ihfg x hx ρ' hΓ'
          simpa only [ETm.denoteIn_open, snoc_empty, ETm.denoteIn,
            ETm.denoteIn_castLE_closed, Fin.cons_zero] using hv) ρ hΓ z hz
      simpa only [ETm.denoteIn, ETm.denoteIn_castLE_closed, Fin.cons_zero] using hb.1
    · exact hvf.2
  | @sigma_ext Γ n hn A p q B L hA hB hp hq h1 h2 ihA ihB ihp ihq ih1 ih2 =>
    intro ρ hΓ
    have hvp : RelatedAt T.U ρ Fin.elim0 (.sigma A B) p p := ihp ρ hΓ
    have hvq : RelatedAt T.U ρ Fin.elim0 (.sigma A B) q q := ihq ρ hΓ
    exact ⟨SetSem.sigma_ext hvp.2 hvq.2 (ih1 ρ hΓ).1 (ih2 ρ hΓ).1, hvp.2⟩
  | @symm Γ A a b h ih =>
    intro ρ hΓ
    have hv : RelatedAt T.U ρ Fin.elim0 A a b := ih ρ hΓ
    exact ⟨hv.1.symm, hv.1 ▸ hv.2⟩
  | trans hab hbc ihab ihbc =>
    intro ρ hΓ
    exact ⟨(ihab ρ hΓ).1.trans (ihbc ρ hΓ).1, (ihab ρ hΓ).2⟩
  | conv hn hA ha ihA iha =>
    intro ρ hΓ
    exact ⟨(iha ρ hΓ).1, (ihA ρ hΓ).1 ▸ (iha ρ hΓ).2⟩
  | cumul hn hmn hA ihA =>
    intro ρ hΓ
    exact ⟨(ihA ρ hΓ).1, tower_mono T hmn hn (ihA ρ hΓ).2⟩

/-- A supplied finite model excludes every actual closed bounded Empty equality. -/
theorem no_empty {levels : ℕ} (T : FiniteTower.{u} levels) {a b : ETm 0} :
    ¬ ECtx.JEqB levels ∅ .nil .empty a b := by
  intro h
  have hv := sound T (fun _ hj => False.elim hj) h (fun _ => ∅) trivial
  exact ZFSet.notMem_empty _ hv.2

end

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FiniteSoundness

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT Silmaril.Logic.SetTheory

universe u

/-- Compatibility name for soundness in the supplied finite universe tower. -/
theorem finite_sound {levels : ℕ} (T : FiniteTower.{u} levels) {H : Set EJdg}
    (hH : ∀ j ∈ H, EJdg.ValidIn T.U j) {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b) : EJdg.ValidIn T.U ⟨Γ, A, a, b⟩ :=
  FiniteSoundness.sound T hH h

/-- Compatibility name for closed Empty consistency at the same rule budget. -/
theorem finite_consistent {levels : ℕ} (T : FiniteTower.{u} levels) {a : ETm 0} :
    ¬ ECtx.JEqB levels ∅ .nil .empty a a :=
  FiniteSoundness.no_empty T

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT
