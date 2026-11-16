module

public import Silmaril.Logic.TypeTheory.LambdaPi.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi

open Silmaril.Logic.TypeTheory.LambdaPi Silmaril.Calculi.LambdaCube

@[simp] theorem map_id (t : Term) : t.mapConstants id = t := by
  have hm : Term.atomMap id = id := funext fun a => by cases a <;> rfl
  simpa only [Term.mapConstants, hm] using Pseudo.mapSorts_id t

@[simp] theorem map_comp (f g : String → String) (t : Term) :
    t.mapConstants (g ∘ f) = (t.mapConstants f).mapConstants g := by
  have hm : Term.atomMap (g ∘ f) = Term.atomMap g ∘ Term.atomMap f :=
    funext fun a => by cases a <;> rfl
  simpa only [Term.mapConstants, hm] using
    (Pseudo.mapSorts_comp (Term.atomMap g) (Term.atomMap f) t).symm

theorem map_rename (f : String → String) (t : Term) (ρ : ℕ → ℕ) :
    Term.mapConstants f (t.rename ρ) = (t.mapConstants f).rename ρ :=
  Pseudo.mapSorts_rename (Term.atomMap f) ρ t

theorem map_subst (f : String → String) (t : Term) (σ : ℕ → Term) :
    Term.mapConstants f (t.subst σ) = (t.mapConstants f).subst (fun i => (σ i).mapConstants f) :=
  Pseudo.mapSorts_subst (Term.atomMap f) σ t

theorem map_substOne (f : String → String) (b a : Term) :
    Term.mapConstants f (b.substOne a) = (b.mapConstants f).substOne (a.mapConstants f) :=
  Pseudo.mapSorts_substOne (Term.atomMap f) b a

theorem map_scoped (f : String → String) (t : Term) : ∀ {n}, t.Scoped n →
    (t.mapConstants f).Scoped n := by
  induction t with
  | sort a => intro n _; cases a <;> trivial
  | var _ => exact fun h => h
  | app _ _ ihf iha => exact fun h => ⟨ihf h.1, iha h.2⟩
  | lam _ _ ihA ihb => exact fun h => ⟨ihA h.1, ihb h.2⟩
  | pi _ _ ihA ihB => exact fun h => ⟨ihA h.1, ihB h.2⟩

theorem beta_conversion {C : Calculus} {t u : Term} (h : Pseudo.Conv t u) :
    C.Conversion t u := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | beta _ _ _ => exact .beta _ _ _
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem lf_conversion (declared : String → Term → Prop) {t u : Term}
    (h : (Calculus.lf declared).Conversion t u) : Pseudo.Conv t u := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | beta _ _ _ => exact .beta _ _ _
  | rewrite r hr _ => exact (Set.notMem_empty r hr).elim
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem derives_bind {C : Calculus} {H K : Set Judgment}
    (hHK : ∀ J ∈ H, Derives C K J) {J : Judgment} (h : Derives C H J) : Derives C K J := by
  induction h with
  | hyp h => exact hHK _ h
  | type => exact .type
  | constant hd _ ih => exact .constant hd ih
  | var _ ih => exact .var ih
  | weak _ _ iht ihB => exact .weak iht ihB
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ ihb ihpi => exact .lam ihb ihpi
  | app _ _ ihf iha => exact .app ihf iha
  | conv _ heq _ iht ihB => exact .conv iht heq ihB

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi
