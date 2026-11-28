module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Defs

/-! # Exact typing and constructor-route soundness of the row checker -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRouteCheck

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)] [DecidableEq κ]

theorem synth {a : Tm Φ} {Γ : VCtx (Ty κ)} {A : Ty κ}
    (ok : a.synthRouteType? Γ = some A) :
    a.HasType Γ A ∧ TypeDetermined Γ a A ∧ DeterminedTerm Γ a A := by
  induction a generalizing A with
  | var i =>
      exact ⟨.var ok, fun _ h => by cases h with
        | var h => exact Option.some.inj (h.symm.trans ok), .var ok⟩
  | unit =>
      cases Option.some.inj ok
      exact ⟨.unit, fun _ h => by cases h; rfl, .unit⟩
  | op p a ih =>
      simp only [Tm.synthRouteType?, Option.bind_eq_some_iff] at ok
      obtain ⟨B, found, checked⟩ := ok
      split at checked
      · rename_i h
        subst B
        cases Option.some.inj checked
        obtain ⟨typed, _, inner⟩ := ih found
        exact ⟨.op typed, fun _ h => by cases h; rfl, .op inner⟩
      · contradiction
  | pair a b iha ihb =>
      simp only [Tm.synthRouteType?, Option.bind_eq_some_iff, Option.some.injEq] at ok
      obtain ⟨B, ha, D, hb, rfl⟩ := ok
      obtain ⟨ta, ua, ea⟩ := iha ha
      obtain ⟨tb, ub, eb⟩ := ihb hb
      refine ⟨.pair ta tb, ?_, .pair ea eb⟩
      intro T h
      cases h with
      | pair h₁ h₂ => rw [ua _ h₁, ub _ h₂]; rfl
  | let₁ | let₂ | inl | inr | case | abort => contradiction

private theorem strip {a b : Tm Φ} {tag : Option CaseTag} (ok : a.routePayload? tag = some b) :
    a = match tag with | none => b | some t => t.inject b := by
  cases tag with
  | none => exact Option.some.inj ok
  | some t => cases t <;> cases a <;> first | contradiction | cases Option.some.inj ok; rfl

theorem routes {layout : RouteLayout κ} {Γ : VCtx (Ty κ)} {r s : Region Φ}
    (ok : r.checkRoutes? layout Γ = some s) : CheckedRoutes layout Γ s r := by
  induction r generalizing Γ s with
  | br i arg =>
      cases hit : layout[i]? with
      | none => simp [Region.checkRoutes?, hit] at ok
      | some label =>
          obtain ⟨A, tag⟩ := label
          simp only [Region.checkRoutes?, hit, Option.bind_eq_some_iff] at ok
          obtain ⟨a, stripped, checked⟩ := ok
          cases found : a.synthRouteType? Γ with
          | none => simp [found] at checked
          | some B =>
              simp only [found] at checked
              split at checked
              · rename_i eq
                subst B
                cases Option.some.inj checked
                obtain ⟨typed, _, uniform⟩ := synth found
                cases tag with
                | none =>
                    have eq : arg = a := strip stripped
                    subst arg
                    exact .plain hit typed uniform
                | some t =>
                    have eq : arg = t.inject a := strip stripped
                    subst arg
                    exact .tagged hit typed uniform
              · contradiction
  | case a l r ihl ihr =>
      cases found : a.synthRouteType? Γ with
      | none => simp [Region.checkRoutes?, found] at ok
      | some T =>
          cases T <;> simp [Region.checkRoutes?, found, Option.bind_eq_some_iff] at ok
          obtain ⟨l', hl, r', hr, rfl⟩ := ok
          obtain ⟨typed, unique, arg⟩ := synth found
          exact .case typed unique arg (ihl hl) (ihr hr)
  | let₁ | let₂ | cfg => contradiction

omit [DecidableEq κ] in
theorem typed {layout : RouteLayout κ} {Γ : VCtx (Ty κ)} {r s : Region Φ}
    (route : CheckedRoutes layout Γ r s) : r.HasType Γ (layout.map Prod.fst) := by
  induction route with
  | plain hit ht _ | tagged hit ht _ =>
      refine .br ?_ ht
      simp only [At, List.getElem?_map, hit, Option.map_some]
  | case ht _ _ _ _ yes no => exact .case ht yes no

section ValueMaps

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

universe u₁ v₁
variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty κ) V)

omit [DecidableEq κ] in
theorem model_routes {layout : RouteLayout κ} {Γ : VCtx (Ty κ)} {r s : Region Φ}
    {L K : LCtx (Ty κ)} {Y : V} {left : labelObj M L ⟶ Y} {right : labelObj M K ⟶ Y}
    (route : CheckedRoutes layout Γ r s)
    (plain : ∀ i A, layout[i]? = some (A, none) →
      ∃ (hl : At L i A) (hr : At K i A), labelInject M i hl ≫ left = labelInject M i hr ≫ right)
    (tagged : ∀ i A tag, layout[i]? = some (A, some tag) →
      ∃ (D : Ty κ) (hl : At L i A) (hr : At K i (tag.sumType A D)),
        labelInject M i hl ≫ left = tag.injection M A D ≫ labelInject M i hr ≫ right) :
    RegionConstructorRoutes M left right Γ r s := by
  induction route with
  | plain hit _ arg =>
      obtain ⟨hl, hr, eq⟩ := plain _ _ hit
      exact .br hl hr arg eq
  | @tagged _ _ _ _ tag hit _ arg =>
      obtain ⟨_, hl, hr, eq⟩ := tagged _ _ tag hit
      cases tag
      · exact .inl hl hr arg eq
      · exact .inr hl hr arg eq
  | case _ unique arg _ _ yes no => exact .case unique arg yes no

end ValueMaps

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRouteCheck
