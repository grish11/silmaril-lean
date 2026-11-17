module

public import Silmaril.Games.DivCompAns.Defs
public import Silmaril.Games.DivComp.Thms
import Silmaril.Proofs.Games.DivCompAns.Zip

/-!
# Composition seen through the answers of the lower component (proofs)

See `Silmaril.Games.DivCompAns.Thms`.
-/

public section

namespace Silmaril.Proofs.Games.DivCompAns

open Silmaril.Games Silmaril.Games.DStrategy

universe u

variable {E F G : Sig.{u}}

/-- Answers below of a prefix. -/
theorem lAnsIn_of_prefix {R : (m : E.Op) → E.Ar m → Prop} {s t : List (Move E F)}
    (h : LAnsIn R t) (hs : s <+: t) : LAnsIn R s :=
  fun _ _ hx => h _ _ (hs.subset hx)

/-- The answers the upper trace receives are answers the lower trace gives. -/
theorem lAnsIn_of_zip_right {R : (m : F.Op) → F.Ar m → Prop} {s : List (Move E F)}
    {t : List (Move F G)} {p : List (Move E G)} (h : Zip s t p) (hs : RAnsIn R s) :
    LAnsIn R t :=
  fun _ _ hx => hs _ _ (zip_inl_mem_right h hx)

/-- The answers the lower trace receives are visible. -/
theorem lAnsIn_of_zip_left {R : (m : E.Op) → E.Ar m → Prop} {s : List (Move E F)}
    {t : List (Move F G)} {p : List (Move E G)} (h : Zip s t p) (hp : LAnsIn R p) :
    LAnsIn R s :=
  fun _ _ hx => hp _ _ (zip_inl_mem_left h hx)

/-! ## Composition with an `R`-answering strategy below -/

theorem comp_eq_of_ansPart {R : (m : F.Op) → F.Ar m → Prop} {σ : DStrategy E F}
    {τ' τ : DStrategy F G} (hσ : σ.AnswersIn R) (h : τ'.AnsPart R τ) :
    σ.comp τ' = σ.comp τ := by
  refine le_antisymm (comp_mono le_rfl h.1) ⟨?_, ?_, ?_⟩
  · rintro p ⟨s, hs, t, ht, hz⟩
    exact ⟨s, hs, t, h.2.1 _ ht (lAnsIn_of_zip_right hz (hσ _ hs)), hz⟩
  · rintro p (⟨s, t, hz, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ | ⟨i, hi⟩)
    · exact mem_div_comp_of_left hs
        (h.2.1 _ ht (lAnsIn_of_zip_right hz (hσ _ (σ.div_mem hs)))) hz
    · exact mem_div_comp_of_right hs (h.2.2.1 _ ht (lAnsIn_of_zip_right hz (hσ _ hs))) hz
    · exact mem_div_comp_of_chatter (i.ansRight hσ h) hi
  · rintro _ ⟨i, hu, rfl⟩
    exact ⟨i.ansRight hσ h, hu, rfl⟩

/-! ## The `R`-answered part under composition above -/

theorem ansPart_comp {R : (m : E.Op) → E.Ar m → Prop} {τ' τ : DStrategy E F}
    (h : τ'.AnsPart R τ) (ρ : DStrategy F G) : (τ'.comp ρ).AnsPart R (τ.comp ρ) := by
  refine ⟨comp_mono h.1 le_rfl, ?_, ?_, ?_⟩
  · rintro p ⟨s, hs, t, ht, hz⟩ hp
    exact ⟨s, h.2.1 _ hs (lAnsIn_of_zip_left hz hp), t, ht, hz⟩
  · rintro p (⟨s, t, hz, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ | ⟨i, hi⟩) hp
    · exact mem_div_comp_of_left (h.2.2.1 _ hs (lAnsIn_of_zip_left hz hp)) ht hz
    · exact mem_div_comp_of_right (h.2.1 _ hs (lAnsIn_of_zip_left hz hp)) ht hz
    · exact mem_div_comp_of_chatter (i.ansLeft h fun n => hi n ▸ hp) hi
  · rintro _ ⟨i, hu, rfl⟩ hJ
    exact ⟨i.ansLeft h fun n => hJ _ ⟨n, List.prefix_refl _⟩, hu, rfl⟩

/-! ## Handlers -/

section Handler

variable {R : (m : F.Op) → F.Ar m → Prop} {h : Handler E F}

/-- The invariant of a handler's runs: every return value still reachable satisfies `R`. -/
def HInv (R : (m : F.Op) → F.Ar m → Prop) (h : Handler E F) :
    h.toReduction.toLTS.State → Prop
  | .idle => True
  | .run q c => Prog.AllRet (R q) (show Prog E (F.Ar q) from c)
  | .wait q _ k => ∀ n, Prog.AllRet (R q) (show Prog E (F.Ar q) from k n)

theorem run_rAnsIn (hh : ∀ q, Prog.AllRet (R q) (h q)) {x y : h.toReduction.toLTS.State}
    {s : List (Move E F)} (hr : h.toReduction.toLTS.Run x s y) (hx : HInv R h x) :
    RAnsIn R s := by
  induction hr with
  | nil => intro _ _ hm; simp at hm
  | tau hst _ ih =>
    cases hst with
    | tau hc => exact hc.elim
  | vis hst _ ih =>
    intro m n hm
    rcases List.mem_cons.1 hm with hm | hm
    · cases hst with
      | ask => cases hm
      | call => cases hm
      | resume => cases hm
      | ret hd =>
        cases hm
        have hd : _ = Prog.pure _ := hd
        simp only [HInv, hd, Prog.AllRet] at hx
        exact hx
    · refine ih ?_ _ _ hm
      cases hst with
      | ask q => exact hh q
      | call hc =>
        have hc : _ = Prog.call _ _ := hc
        simp only [HInv, hc, Prog.AllRet] at hx ⊢
        exact hx
      | resume q m k n => exact hx n
      | ret => trivial

theorem answersIn_ofHandler (hh : ∀ q, Prog.AllRet (R q) (h q)) :
    (DStrategy.ofHandler h).AnswersIn R := by
  rintro p ⟨-, s, hs, hp⟩ m n hm
  have hs : RAnsIn R s := by
    rcases hs with rfl | ⟨⟨y, hr⟩, -⟩
    · intro _ _ hm; simp at hm
    · exact run_rAnsIn hh hr trivial
  rcases hp with hp | ⟨p₀, o, rfl, hp₀, ho⟩
  · exact hs _ _ (hp.subset hm)
  · rcases List.mem_append.1 hm with hm | hm
    · exact hs _ _ (hp₀.subset hm)
    · rw [List.mem_singleton] at hm
      subst hm
      exact ho.elim

end Handler

end Silmaril.Proofs.Games.DivCompAns
