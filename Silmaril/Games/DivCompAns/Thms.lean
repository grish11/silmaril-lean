module

public import Silmaril.Games.DivCompAns.Defs
public import Silmaril.Games.DivComp.Thms
import Silmaril.Proofs.Games.DivCompAns.Basic

/-!
# Composition seen through the answers of the lower component: theorems

* `comp_eq_of_ansPart`: if `σ` answers in `R` and `τ'` is the `R`-answered part of `τ`, then
  `σ.comp τ' = σ.comp τ`, on all observations: finite plays, local divergences, divergence by
  infinite hidden chatter, and infinite plays. The chatter and infinite-play witnesses are the
  same interactions, lifted coherently (`InfInteraction.ansRight`).
* `ansPart_comp`: if `τ'` is the `R`-answered part of `τ`, then `τ'.comp ρ` is the `R`-answered
  part of `τ.comp ρ` (interactions lifted by `InfInteraction.ansLeft`).
* `answersIn_ofHandler`: a handler all of whose programs return in `R` answers in `R`.
* `lAnsIn_of_zip_right`, `lAnsIn_of_zip_left`, `lAnsIn_of_prefix`: the answers the upper trace of
  an interaction receives are answers of the lower trace; those the lower trace receives are
  visible; answers of prefixes.
-/

public section

namespace Silmaril.Games

universe u

variable {E F G : Sig.{u}}

/-- Answers below of a prefix. -/
theorem lAnsIn_of_prefix {R : (m : E.Op) → E.Ar m → Prop} {s t : List (Move E F)}
    (h : LAnsIn R t) (hs : s <+: t) : LAnsIn R s :=
  fun _ _ hx => h _ _ (hs.subset hx)

/-- The answers the upper trace of an interaction receives are answers of the lower trace. -/
theorem lAnsIn_of_zip_right {R : (m : F.Op) → F.Ar m → Prop} {s : List (Move E F)}
    {t : List (Move F G)} {p : List (Move E G)} (h : Zip s t p) (hs : RAnsIn R s) :
    LAnsIn R t :=
  Silmaril.Proofs.Games.DivCompAns.lAnsIn_of_zip_right h hs

/-- The answers the lower trace of an interaction receives are visible. -/
theorem lAnsIn_of_zip_left {R : (m : E.Op) → E.Ar m → Prop} {s : List (Move E F)}
    {t : List (Move F G)} {p : List (Move E G)} (h : Zip s t p) (hp : LAnsIn R p) :
    LAnsIn R s :=
  Silmaril.Proofs.Games.DivCompAns.lAnsIn_of_zip_left h hp

namespace DStrategy

/-- **Composition with an `R`-answering strategy only sees the `R`-answered part**, on finite
plays, divergences (hidden chatter included) and infinite plays. -/
theorem comp_eq_of_ansPart {R : (m : F.Op) → F.Ar m → Prop} {σ : DStrategy E F}
    {τ' τ : DStrategy F G} (hσ : σ.AnswersIn R) (h : τ'.AnsPart R τ) :
    σ.comp τ' = σ.comp τ :=
  Silmaril.Proofs.Games.DivCompAns.comp_eq_of_ansPart hσ h

/-- **The `R`-answered part is preserved by composition above.** -/
theorem ansPart_comp {R : (m : E.Op) → E.Ar m → Prop} {τ' τ : DStrategy E F}
    (h : τ'.AnsPart R τ) (ρ : DStrategy F G) : (τ'.comp ρ).AnsPart R (τ.comp ρ) :=
  Silmaril.Proofs.Games.DivCompAns.ansPart_comp h ρ

/-- Every strategy is its own `R`-answered part. -/
theorem ansPart_refl (R : (m : E.Op) → E.Ar m → Prop) (τ : DStrategy E F) : τ.AnsPart R τ :=
  ⟨le_rfl, fun _ h _ => h, fun _ h _ => h, fun _ h _ => h⟩

/-- **A handler all of whose programs return in `R` answers in `R`.** -/
theorem answersIn_ofHandler {R : (m : F.Op) → F.Ar m → Prop} {h : Handler E F}
    (hh : ∀ q, Prog.AllRet (R q) (h q)) : (DStrategy.ofHandler h).AnswersIn R :=
  Silmaril.Proofs.Games.DivCompAns.answersIn_ofHandler hh

/-- The coherent lift on the right keeps the chains. -/
theorem InfInteraction.ansRight_chains {R : (m : F.Op) → F.Ar m → Prop} {σ : DStrategy E F}
    {τ' τ : DStrategy F G} (hσ : σ.AnswersIn R) (h : τ'.AnsPart R τ) (i : InfInteraction σ τ) :
    (i.ansRight hσ h).p = i.p ∧ (i.ansRight hσ h).s = i.s ∧ (i.ansRight hσ h).t = i.t :=
  ⟨rfl, rfl, rfl⟩

/-- The coherent lift on the left keeps the chains. -/
theorem InfInteraction.ansLeft_chains {R : (m : E.Op) → E.Ar m → Prop} {τ' τ : DStrategy E F}
    {ρ : DStrategy F G} (h : τ'.AnsPart R τ) (i : InfInteraction τ ρ)
    (hp : ∀ n, LAnsIn R (i.p n)) :
    (i.ansLeft h hp).p = i.p ∧ (i.ansLeft h hp).s = i.s ∧ (i.ansLeft h hp).t = i.t :=
  ⟨rfl, rfl, rfl⟩

end DStrategy

end Silmaril.Games
