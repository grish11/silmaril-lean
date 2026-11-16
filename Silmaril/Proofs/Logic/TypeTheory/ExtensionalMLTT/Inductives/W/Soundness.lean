module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Soundness
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Rules.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.BinderSemantics
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetUniverse

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

universe u
open ZFSet
open Silmaril.Logic.SetTheory

noncomputable section

/-- Context satisfaction validates every declared-variable lookup. -/
theorem Ctx.Lookup.sat {Γ : Ctx} {x : String} {A : Tm 0}
    (hx : Γ.Lookup x A) (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    (hΓ : Γ.Sat T ρ) : ρ x ∈ A.denote T ρ Fin.elim0 := by
  induction hx with
  | here => exact hΓ.2
  | there _ _ _ _ _ _ _ ih => exact ih hΓ.1

/-- The cofinite natural-recursion step premise is valid at every natural input. -/
private theorem natstep_valid (T : SetHierarchy.{u}) {Γ : Ctx} {C s s' : Tm 1}
    {L : Finset String}
    (h : ∀ x ∉ L, (⟨Γ.cons x .nats,
      Tm.arr (C.open x) (C.lst (.succ (.fv x))), s.open x, s'.open x⟩ : Jdg).Valid T)
    (ρ : String → ZFSet.{u}) (hΓ : Γ.Sat T ρ) (m : ZFSet.{u}) (hm : m ∈ omega) :
    s.denote T ρ (Fin.cons m Fin.elim0) = s'.denote T ρ (Fin.cons m Fin.elim0) ∧
    s.denote T ρ (Fin.cons m Fin.elim0) ∈
      SetSem.pi (C.denote T ρ (Fin.cons m Fin.elim0))
        (fun _ => C.denote T ρ (Fin.cons (insert m m) Fin.elim0)) := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ Γ.fvs ∪ C.fvs ∪ s.fvs ∪ s'.fvs)
  have hxL : x ∉ L := fun h => hx (by simp [h])
  have hxΓ : x ∉ Γ.fvs := fun h => hx (by simp [h])
  have hxC : x ∉ C.fvs := fun h => hx (by simp [h])
  have hxs : x ∉ s.fvs := fun h => hx (by simp [h])
  have hxs' : x ∉ s'.fvs := fun h => hx (by simp [h])
  have hΓ' := (Ctx.sat_update T ρ Γ x m hxΓ).2 hΓ
  have hv := h x hxL (Function.update ρ x m) ⟨hΓ', by simpa [Tm.denote] using hm⟩
  change (s.open x).denote T (Function.update ρ x m) Fin.elim0 = _ ∧
    (s.open x).denote T (Function.update ρ x m) Fin.elim0 ∈
      (Tm.arr (C.open x) (C.lst (.succ (.fv x)))).denote T (Function.update ρ x m) Fin.elim0 at hv
  rw [Tm.denote_open_update T ρ s x m hxs,
    Tm.denote_open_update T ρ s' x m hxs', Tm.denote_arr,
    Tm.denote_open_update T ρ C x m hxC, Tm.denote_lst0] at hv
  simp only [Tm.denote, Function.update_self] at hv
  rw [Tm.denote_update T ρ _ C x m hxC] at hv
  exact hv

/-- Equality and typing at one environment, including environments under a binder. -/
private abbrev RelatedAt (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (A a b : Tm k) : Prop :=
  a.denote T ρ β = b.denote T ρ β ∧ a.denote T ρ β ∈ A.denote T ρ β

/-- Every inference rule preserves validity in a hierarchy of set universes. -/
theorem Ctx.JEqH.sound (T : SetHierarchy.{u}) {H : Set Jdg}
    (hH : ∀ j ∈ H, Jdg.Valid T j) {Γ : Ctx} {A a b : Tm 0}
    (h : Ctx.JEqH H Γ A a b) : Jdg.Valid T ⟨Γ, A, a, b⟩ := by
  induction h with
  | hyp hj => exact hH _ hj
  | nil_ok =>
    intro ρ hΓ
    exact ⟨rfl, by simp [Tm.denote]⟩
  | cons_ok hΓ hx hA ihΓ ihA =>
    intro ρ hΓ
    exact ⟨rfl, by simp [Tm.denote]⟩
  | var hΓ hx ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, hx.sat T ρ hΓ⟩
  | univ hΓ ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, T.mem_succ _⟩
  | empty hΓ ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, (T.isGrothendieck _).empty_mem⟩
  | unit hΓ ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, (T.isGrothendieck _).singleton_mem (T.isGrothendieck _).empty_mem⟩
  | nats hΓ ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, (T.isGrothendieck _).omega_mem⟩
  | zero hΓ ihΓ =>
    intro ρ hΓ
    exact ⟨rfl, omega_zero⟩
  | @succ Γ m m' h ih =>
    intro ρ hΓ
    have hv : RelatedAt T ρ Fin.elim0 .nats m m' := ih ρ hΓ
    exact ⟨congrArg (fun x => insert x x) hv.1, omega_succ hv.2⟩
  | @pi Γ n A A' B B' L hA hB ihA ihB =>
    show Jdg.Valid T ⟨Γ, .univ n, .pi A B, .pi A' B'⟩
    intro ρ hΓ
    have ha : RelatedAt T ρ Fin.elim0 (.univ n) A A' := ihA ρ hΓ
    have hb : ∀ z ∈ A.denote T ρ Fin.elim0,
        RelatedAt T ρ (Fin.cons z Fin.elim0) (.univ n) B B' :=
      binder_valid T (Γ := Γ) (A := A) (C := .univ n) (a := B) (b := B') (L := L)
      (by intro x hx; simpa only [Tm.open] using ihB x hx) ρ hΓ
    constructor
    · change SetSem.pi _ _ = SetSem.pi _ _
      rw [ha.1]
      apply SetSem.pi_congr
      intro z hz
      exact (hb z (ha.1.symm ▸ hz)).1
    · exact SetSem.pi_mem (T.isGrothendieck n) ha.2 (fun z hz => (hb z hz).2)
  | @sigma Γ n A A' B B' L hA hB ihA ihB =>
    show Jdg.Valid T ⟨Γ, .univ n, .sigma A B, .sigma A' B'⟩
    intro ρ hΓ
    have ha : RelatedAt T ρ Fin.elim0 (.univ n) A A' := ihA ρ hΓ
    have hb : ∀ z ∈ A.denote T ρ Fin.elim0,
        RelatedAt T ρ (Fin.cons z Fin.elim0) (.univ n) B B' :=
      binder_valid T (Γ := Γ) (A := A) (C := .univ n) (a := B) (b := B') (L := L)
      (by intro x hx; simpa only [Tm.open] using ihB x hx) ρ hΓ
    constructor
    · change SetSem.sigma _ _ = SetSem.sigma _ _
      rw [ha.1]
      apply SetSem.sigma_congr
      intro z hz
      exact (hb z (ha.1.symm ▸ hz)).1
    · exact SetSem.sigma_mem (T.isGrothendieck n) ha.2 (fun z hz => (hb z hz).2)
  | @id Γ n A A' a a' b b' hA ha hb ihA iha ihb =>
    intro ρ hΓ
    have hvA : RelatedAt T ρ Fin.elim0 A a a' := iha ρ hΓ
    have hvB : RelatedAt T ρ Fin.elim0 A b b' := ihb ρ hΓ
    constructor
    · change SetSem.truth _ = SetSem.truth _
      rw [hvA.1, hvB.1]
    · exact SetSem.truth_mem (T.isGrothendieck n) _
  | @abs Γ n A A' B b b' L hA hB hb ihA ihB ihb =>
    show Jdg.Valid T ⟨Γ, .pi A B, .abs A b, .abs A' b'⟩
    intro ρ hΓ
    have ha : RelatedAt T ρ Fin.elim0 (.univ n) A A' := ihA ρ hΓ
    have hvb : ∀ z ∈ A.denote T ρ Fin.elim0,
        RelatedAt T ρ (Fin.cons z Fin.elim0) B b b' :=
      binder_valid T (Γ := Γ) (A := A) (C := B) (a := b) (b := b') (L := L) ihb ρ hΓ
    constructor
    · change SetSem.lam _ _ = SetSem.lam _ _
      rw [ha.1]
      apply SetSem.lam_congr
      intro z hz
      exact (hvb z (ha.1.symm ▸ hz)).1
    · exact SetSem.lam_mem_pi (fun z hz => (hvb z hz).2)
  | @app Γ n A f f' a a' B L hA hB hf ha ihA ihB ihf iha =>
    intro ρ hΓ
    have hvf : RelatedAt T ρ Fin.elim0 (.pi A B) f f' := ihf ρ hΓ
    have hva : RelatedAt T ρ Fin.elim0 A a a' := iha ρ hΓ
    constructor
    · exact congrArg₂ SetSem.app hvf.1 hva.1
    · rw [Tm.denote_lst0]
      exact SetSem.app_mem_of_mem_pi hvf.2 hva.2
  | @pair Γ n A a a' b b' B L hA hB ha hb ihA ihB iha ihb =>
    intro ρ hΓ
    have hva : RelatedAt T ρ Fin.elim0 A a a' := iha ρ hΓ
    have hvb : RelatedAt T ρ Fin.elim0 (B.lst a) b b' := ihb ρ hΓ
    constructor
    · exact congrArg₂ SetSem.pair hva.1 hvb.1
    · apply SetSem.pair_mem_sigma.2
      exact ⟨hva.2, by simpa only [Tm.denote_lst0] using hvb.2⟩
  | @fst Γ n A p p' B L hA hB hp ihA ihB ihp =>
    intro ρ hΓ
    have hvp : RelatedAt T ρ Fin.elim0 (.sigma A B) p p' := ihp ρ hΓ
    exact ⟨congrArg SetSem.fst hvp.1, SetSem.fst_mem_of_mem_sigma hvp.2⟩
  | @snd Γ n A p p' B L hA hB hp ihA ihB ihp =>
    intro ρ hΓ
    have hvp : RelatedAt T ρ Fin.elim0 (.sigma A B) p p' := ihp ρ hΓ
    constructor
    · exact congrArg SetSem.snd hvp.1
    · rw [Tm.denote_lst0]
      exact SetSem.snd_mem_of_mem_sigma hvp.2
  | @natrec Γ n C C' s s' z z' m m' L hC hz hs hm ihC ihz ihs ihm =>
    show Jdg.Valid T ⟨Γ, C.lst m, .natrec C s z m, .natrec C' s' z' m'⟩
    intro ρ hΓ
    have hvz : RelatedAt T ρ Fin.elim0 (C.lst .zero) z z' := ihz ρ hΓ
    have hvm : RelatedAt T ρ Fin.elim0 .nats m m' := ihm ρ hΓ
    have hvstep : ∀ m ∈ omega,
        s.denote T ρ (Fin.cons m Fin.elim0) = s'.denote T ρ (Fin.cons m Fin.elim0) ∧
        s.denote T ρ (Fin.cons m Fin.elim0) ∈
          SetSem.pi (C.denote T ρ (Fin.cons m Fin.elim0))
            (fun _ => C.denote T ρ (Fin.cons (insert m m) Fin.elim0)) :=
      natstep_valid T ihs ρ hΓ
    let B : ZFSet.{u} → ZFSet.{u} := fun a => C.denote T ρ (Fin.cons a Fin.elim0)
    let step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
      fun a r => SetSem.app (s.denote T ρ (Fin.cons a Fin.elim0)) r
    have hzB : z.denote T ρ Fin.elim0 ∈ B ∅ := by
      simpa only [Tm.denote_lst0, Tm.denote, B] using hvz.2
    have hsB : ∀ a ∈ omega, ∀ r ∈ B a, step a r ∈ B (insert a a) := by
      intro a ha r hr
      exact SetSem.app_mem_of_mem_pi (hvstep a ha).2 hr
    constructor
    · change SetSem.natrec _ _ _ = SetSem.natrec _ _ _
      rw [← hvm.1]
      apply SetSem.natrec_congr (B := B) hvz.1 hzB hsB _ hvm.2
      intro a ha r hr
      exact congrArg (fun f => SetSem.app f r) (hvstep a ha).1
    · rw [Tm.denote_lst0]
      exact SetSem.natrec_mem hzB hsB hvm.2
  | refl ha iha =>
    intro ρ hΓ
    exact ⟨rfl, SetSem.mem_truth.2 ⟨rfl, rfl⟩⟩
  | absurd hC he ihC ihe =>
    intro ρ hΓ
    exact (notMem_empty _ (ihe ρ hΓ).2).elim
  | @beta_app Γ n A a B b L hA hB hb ha ihA ihB ihb iha =>
    show Jdg.Valid T ⟨Γ, B.lst a, .app (.abs A b) a, b.lst a⟩
    intro ρ hΓ
    have hva : RelatedAt T ρ Fin.elim0 A a a := iha ρ hΓ
    have hvb : RelatedAt T ρ (Fin.cons (a.denote T ρ Fin.elim0) Fin.elim0) B b b :=
      binder_valid T (Γ := Γ) (A := A) (C := B) (a := b) (b := b) (L := L) ihb ρ hΓ _ hva.2
    constructor
    · simpa only [Tm.denote, Tm.denote_lst0] using
        SetSem.app_lam (fun z => b.denote T ρ (Fin.cons z Fin.elim0)) hva.2
    · rw [Tm.denote_lst0]
      change SetSem.app (SetSem.lam _ _) _ ∈ _
      rw [SetSem.app_lam _ hva.2]
      exact hvb.2
  | beta_fst hA hB ha hb ihA ihB iha ihb =>
    intro ρ hΓ
    constructor
    · exact SetSem.fst_pair _ _
    · simpa only [Tm.denote, SetSem.fst_pair] using (iha ρ hΓ).2
  | beta_snd hA hB ha hb ihA ihB iha ihb =>
    intro ρ hΓ
    constructor
    · exact SetSem.snd_pair _ _
    · simpa only [Tm.denote, SetSem.snd_pair] using (ihb ρ hΓ).2
  | beta_natrec_zero hC hz hs ihC ihz ihs =>
    intro ρ hΓ
    constructor
    · exact SetSem.natrec_zero _ _
    · simpa only [Tm.denote, SetSem.natrec_zero] using (ihz ρ hΓ).2
  | @beta_natrec_succ Γ n C s z m L hC hz hs hm ihC ihz ihs ihm =>
    show Jdg.Valid T ⟨Γ, C.lst (.succ m), .natrec C s z (.succ m), .app (s.lst m) (.natrec C s z m)⟩
    intro ρ hΓ
    have hvz : RelatedAt T ρ Fin.elim0 (C.lst .zero) z z := ihz ρ hΓ
    have hvm : RelatedAt T ρ Fin.elim0 .nats m m := ihm ρ hΓ
    have hvstep : ∀ m ∈ omega,
        s.denote T ρ (Fin.cons m Fin.elim0) = s.denote T ρ (Fin.cons m Fin.elim0) ∧
        s.denote T ρ (Fin.cons m Fin.elim0) ∈
          SetSem.pi (C.denote T ρ (Fin.cons m Fin.elim0))
            (fun _ => C.denote T ρ (Fin.cons (insert m m) Fin.elim0)) :=
      natstep_valid T ihs ρ hΓ
    let B : ZFSet.{u} → ZFSet.{u} := fun a => C.denote T ρ (Fin.cons a Fin.elim0)
    let step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
      fun a r => SetSem.app (s.denote T ρ (Fin.cons a Fin.elim0)) r
    have hzB : z.denote T ρ Fin.elim0 ∈ B ∅ := by
      simpa only [Tm.denote_lst0, Tm.denote, B] using hvz.2
    have hsB : ∀ a ∈ omega, ∀ r ∈ B a, step a r ∈ B (insert a a) := by
      intro a ha r hr
      exact SetSem.app_mem_of_mem_pi (hvstep a ha).2 hr
    constructor
    · simpa only [Tm.denote, Tm.denote_lst0] using
        SetSem.natrec_succ (z.denote T ρ Fin.elim0) step hvm.2
    · rw [Tm.denote_lst0]
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
  | @pi_ext Γ n A f g B L hA hB hf hg hfg ihA ihB ihf ihg ihfg =>
    show Jdg.Valid T ⟨Γ, .pi A B, f, g⟩
    intro ρ hΓ
    have hvf : RelatedAt T ρ Fin.elim0 (.pi A B) f f := ihf ρ hΓ
    have hvg : RelatedAt T ρ Fin.elim0 (.pi A B) g g := ihg ρ hΓ
    constructor
    · show f.denote T ρ Fin.elim0 = g.denote T ρ Fin.elim0
      apply SetSem.pi_ext hvf.2 hvg.2
      intro z hz
      have hb :
          (Tm.app (f.castLE (by omega)) (.bv 0)).denote T ρ (Fin.cons z Fin.elim0) =
            (Tm.app (g.castLE (by omega)) (.bv 0)).denote T ρ (Fin.cons z Fin.elim0) ∧
          (Tm.app (f.castLE (by omega)) (.bv 0)).denote T ρ (Fin.cons z Fin.elim0) ∈
            B.denote T ρ (Fin.cons z Fin.elim0) :=
        binder_valid T (Γ := Γ) (A := A) (C := B) (L := L)
        (a := .app (f.castLE (by omega)) (.bv 0))
        (b := .app (g.castLE (by omega)) (.bv 0))
        (by
          intro x hx ρ' hΓ'
          have hv := ihfg x hx ρ' hΓ'
          simpa only [Tm.denote_open, snoc_empty, Tm.denote,
            Tm.denote_castLE_closed, Fin.cons_zero] using hv) ρ hΓ z hz
      simpa only [Tm.denote, Tm.denote_castLE_closed, Fin.cons_zero] using hb.1
    · exact hvf.2
  | @sigma_ext Γ n A p q B L hA hB hp hq h1 h2 ihA ihB ihp ihq ih1 ih2 =>
    intro ρ hΓ
    have hvp : RelatedAt T ρ Fin.elim0 (.sigma A B) p p := ihp ρ hΓ
    have hvq : RelatedAt T ρ Fin.elim0 (.sigma A B) q q := ihq ρ hΓ
    exact ⟨SetSem.sigma_ext hvp.2 hvq.2 (ih1 ρ hΓ).1 (ih2 ρ hΓ).1, hvp.2⟩
  | @symm Γ A a b h ih =>
    intro ρ hΓ
    have hv : RelatedAt T ρ Fin.elim0 A a b := ih ρ hΓ
    exact ⟨hv.1.symm, hv.1 ▸ hv.2⟩
  | trans hab hbc ihab ihbc =>
    intro ρ hΓ
    exact ⟨(ihab ρ hΓ).1.trans (ihbc ρ hΓ).1, (ihab ρ hΓ).2⟩
  | conv hA ha ihA iha =>
    intro ρ hΓ
    exact ⟨(iha ρ hΓ).1, (ihA ρ hΓ).1 ▸ (iha ρ hΓ).2⟩
  | cumul hmn hA ihA =>
    intro ρ hΓ
    exact ⟨(ihA ρ hΓ).1, T.mono hmn (ihA ρ hΓ).2⟩

  | @wtype Γ n A A' B B' L hA hB ihA ihB =>
    show Jdg.Valid T ⟨Γ, .univ n, .wtype A B, .wtype A' B'⟩
    intro ρ hΓ
    have ha : RelatedAt T ρ Fin.elim0 (.univ n) A A' := ihA ρ hΓ
    have hb : ∀ z ∈ A.denote T ρ Fin.elim0,
        RelatedAt T ρ (Fin.cons z Fin.elim0) (.univ n) B B' :=
      binder_valid T (Γ := Γ) (A := A) (C := .univ n) (a := B) (b := B') (L := L)
        (by intro x hx; simpa only [Tm.open] using ihB x hx) ρ hΓ
    constructor
    · exact WSet.carrier_congr_of_eq ha.1 (fun z hz => (hb z hz).1)
    · exact WSet.carrier_mem (T.isGrothendieck n) ha.2 (fun z hz => (hb z hz).2)
  | @sup Γ n A a a' f f' B L hA hB ha hf ihA ihB iha ihf =>
    show Jdg.Valid T ⟨Γ, .wtype A B, .sup A B a f, .sup A B a' f'⟩
    intro ρ hΓ
    have hva : RelatedAt T ρ Fin.elim0 A a a' := iha ρ hΓ
    have hvf : RelatedAt T ρ Fin.elim0 (.arr (B.lst a) (.wtype A B)) f f' := ihf ρ hΓ
    constructor
    · exact congrArg₂ (WSet.node (A.denote T ρ Fin.elim0)
        (fun z => B.denote T ρ (Fin.cons z Fin.elim0))) hva.1 hvf.1
    · apply WSet.node_mem hva.2
      simpa only [Tm.denote_arr, Tm.denote_lst0, Tm.denote] using hvf.2
  | @wrec Γ n m A s s' t t' B C C' L hA hB hC hs ht ihA ihB ihC ihs iht =>
    show Jdg.Valid T ⟨Γ, C.lst t, .wrec A B C s t, .wrec A B C' s' t'⟩
    intro ρ hΓ
    have hvs : RelatedAt T ρ Fin.elim0 (Tm.wStepType A B C) s s' := ihs ρ hΓ
    have hvt : RelatedAt T ρ Fin.elim0 (.wtype A B) t t' := iht ρ hΓ
    constructor
    · exact congrArg₂ (WSet.wrec (A.denote T ρ Fin.elim0)
        (fun z => B.denote T ρ (Fin.cons z Fin.elim0))) hvs.1 hvt.1
    · rw [Tm.denote_lst0]
      exact WSet.wrec_mem (A := A.denote T ρ Fin.elim0)
        (B := fun z => B.denote T ρ (Fin.cons z Fin.elim0))
        (C := fun z => C.denote T ρ (Fin.cons z Fin.elim0))
        (by simpa only [Tm.denote_wStepType] using hvs.2) hvt.2
  | @beta_wrec Γ n m A s a f B C L hA hB hC hs ha hf ihA ihB ihC ihs iha ihf =>
    show Jdg.Valid T ⟨Γ, C.lst (.sup A B a f), .wrec A B C s (.sup A B a f),
      .app (.app (.app s a) f) (Tm.recChildren A B C s a f)⟩
    intro ρ hΓ
    have hvs : RelatedAt T ρ Fin.elim0 (Tm.wStepType A B C) s s := ihs ρ hΓ
    have hva : RelatedAt T ρ Fin.elim0 A a a := iha ρ hΓ
    have hvf : RelatedAt T ρ Fin.elim0 (.arr (B.lst a) (.wtype A B)) f f := ihf ρ hΓ
    have hfgraph : f.denote T ρ Fin.elim0 ∈
        SetSem.pi (B.denote T ρ (Fin.cons (a.denote T ρ Fin.elim0) Fin.elim0))
          (fun _ => WSet.carrier (A.denote T ρ Fin.elim0)
            (fun z => B.denote T ρ (Fin.cons z Fin.elim0))) := by
      simpa only [Tm.denote_arr, Tm.denote_lst0, Tm.denote] using hvf.2
    constructor
    · simpa only [Tm.denote_recChildren, Tm.denote] using
        WSet.wrec_node (A := A.denote T ρ Fin.elim0)
          (B := fun z => B.denote T ρ (Fin.cons z Fin.elim0))
          (a := a.denote T ρ Fin.elim0) (f := f.denote T ρ Fin.elim0)
          (s.denote T ρ Fin.elim0) hva.2 hfgraph
    · rw [Tm.denote_lst0]
      exact WSet.wrec_mem (A := A.denote T ρ Fin.elim0)
        (B := fun z => B.denote T ρ (Fin.cons z Fin.elim0))
        (C := fun z => C.denote T ρ (Fin.cons z Fin.elim0))
        (by simpa only [Tm.denote_wStepType] using hvs.2)
        (WSet.node_mem (A := A.denote T ρ Fin.elim0)
          (B := fun z => B.denote T ρ (Fin.cons z Fin.elim0))
          (a := a.denote T ρ Fin.elim0) (f := f.denote T ρ Fin.elim0) hva.2 hfgraph)

/-- Soundness of the original hypothesis-free derivations. -/
theorem Ctx.JEq.sound (T : SetHierarchy.{u}) {Γ : Ctx} {A a b : Tm 0}
    (h : Ctx.JEq Γ A a b) : Jdg.Valid T ⟨Γ, A, a, b⟩ :=
  Ctx.JEqH.sound T (fun _ hj => (Set.notMem_empty _ hj).elim) h

/-- A hierarchy model excludes a closed inhabitant of the empty type. -/
theorem Ctx.JEq.consistent (T : SetHierarchy.{u}) {a : Tm 0} :
    ¬ Ctx.JEq .nil .empty a a := by
  intro h
  have hv := h.sound T (fun _ => ∅) trivial
  exact notMem_empty _ hv.2

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
