module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRouteCheck

/-! # Successful route checks give exact and determined typing -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA

open Semantics.Categorical
variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)] [DecidableEq κ]

theorem Tm.synthRouteType?_sound {a : Tm Φ} {Γ : VCtx (Ty κ)} {A : Ty κ}
    (ok : a.synthRouteType? Γ = some A) :
    a.HasType Γ A ∧ TypeDetermined Γ a A ∧ DeterminedTerm Γ a A :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRouteCheck.synth ok

theorem Region.checkRoutes?_sound {layout : RouteLayout κ} {Γ : VCtx (Ty κ)} {r s : Region Φ}
    (ok : r.checkRoutes? layout Γ = some s) : CheckedRoutes layout Γ s r :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRouteCheck.routes ok

omit [DecidableEq κ] in
/-- Read back an exact common typing from the checked operands and branches. -/
theorem CheckedRoutes.hasType {layout : RouteLayout κ} {Γ : VCtx (Ty κ)} {r s : Region Φ}
    (route : CheckedRoutes layout Γ r s) : r.HasType Γ (layout.map Prod.fst) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRouteCheck.typed route

section ValueMaps

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

universe u₁ v₁
variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty κ) V)

omit [DecidableEq κ] in
theorem CheckedRoutes.toConstructorRoutes {layout : RouteLayout κ} {Γ : VCtx (Ty κ)} {r s : Region Φ}
    {L K : LCtx (Ty κ)} {Y : V} {left : labelObj M L ⟶ Y} {right : labelObj M K ⟶ Y}
    (route : CheckedRoutes layout Γ r s)
    (plain : ∀ i A, layout[i]? = some (A, none) →
      ∃ (hl : At L i A) (hr : At K i A), labelInject M i hl ≫ left = labelInject M i hr ≫ right)
    (tagged : ∀ i A tag, layout[i]? = some (A, some tag) →
      ∃ (D : Ty κ) (hl : At L i A) (hr : At K i (tag.sumType A D)),
        labelInject M i hl ≫ left = tag.injection M A D ≫ labelInject M i hr ≫ right) :
    RegionConstructorRoutes M left right Γ r s :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRouteCheck.model_routes M route plain tagged

end ValueMaps

end Silmaril.Isotope.LambdaSSA
