module

public import Silmaril.Logic.TypeTheory.LambdaPi.Category.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi

open Silmaril.Logic.TypeTheory.LambdaPi Silmaril.Calculi.LambdaCube

@[simp] theorem rule_map_id (r : RewriteRule) : r.mapConstants id = r := by
  cases r
  simp only [RewriteRule.mapConstants, map_id]

@[simp] theorem rule_map_comp (f g : String → String) (r : RewriteRule) :
    r.mapConstants (g ∘ f) = (r.mapConstants f).mapConstants g := by
  cases r
  simp only [RewriteRule.mapConstants, map_comp]

@[simp] theorem judgment_map_id (J : Judgment) : J.mapConstants id = J := by
  have hm : Term.mapConstants id = id := funext map_id
  cases J
  simp [Judgment.mapConstants, hm]

@[simp] theorem judgment_map_comp (f g : String → String) (J : Judgment) :
    J.mapConstants (g ∘ f) = (J.mapConstants f).mapConstants g := by
  have hm : Term.mapConstants (g ∘ f) = Term.mapConstants g ∘ Term.mapConstants f :=
    funext (map_comp f g)
  cases J
  simp only [Judgment.mapConstants, hm, List.map_map, Function.comp_apply]

theorem conversion_map {C D : Calculus} (F : Morphism C D) {t u : Term}
    (h : C.Conversion t u) : D.Conversion (t.mapConstants F.constants) (u.mapConstants F.constants) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | beta A b a =>
    simpa only [Term.mapConstants, Pseudo.mapSorts, Term.atomMap, Pseudo.mapSorts_substOne] using
      (Calculus.Conversion.beta (C := D) (A.mapConstants F.constants)
        (b.mapConstants F.constants) (a.mapConstants F.constants))
  | rewrite r hr σ =>
    simpa only [RewriteRule.mapConstants, map_subst] using
      (Calculus.Conversion.rewrite (C := D) (r.mapConstants F.constants) (F.rules r hr)
        (fun i => (σ i).mapConstants F.constants))
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem derives_map {C D : Calculus} (F : Morphism C D) {H : Set Judgment} {J : Judgment}
    (h : Derives C H J) :
    Derives D (Judgment.mapConstants F.constants '' H) (J.mapConstants F.constants) := by
  induction h with
  | hyp h => exact .hyp ⟨_, h, rfl⟩
  | type => exact .type
  | constant hd _ ih => exact .constant (F.declared hd) ih
  | var _ ih =>
    simpa only [Judgment.mapConstants, Term.mapConstants, Pseudo.mapSorts,
      Term.atomMap, List.map_cons, Pseudo.mapSorts_rename] using
      (Derives.var ih)
  | weak _ _ iht ihB =>
    simpa only [Judgment.mapConstants, Term.mapConstants, Pseudo.mapSorts,
      Term.atomMap, List.map_cons, Pseudo.mapSorts_rename] using
      (Derives.weak iht ihB)
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ ihb ihpi => exact .lam ihb ihpi
  | app _ _ ihf iha =>
    simpa only [Judgment.mapConstants, Term.mapConstants, Pseudo.mapSorts,
      Term.atomMap, Pseudo.mapSorts_substOne] using
      (Derives.app ihf iha)
  | conv _ heq _ iht ihB => exact .conv iht (conversion_map F heq) ihB

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi
