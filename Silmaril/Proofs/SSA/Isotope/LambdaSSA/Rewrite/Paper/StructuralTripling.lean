module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.UnitTree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTripling

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory.ComponentTripling (StructuralState UnitTree)
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ThreeCycle (triple transportStep triple_step_unit_tree)

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "J" => projection Seed
local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod

set_option backward.isDefEq.respectTransparency false

private noncomputable def sumMapIso {A B C D : τ} (e : Obj A ≅ Obj C) (f : Obj B ≅ Obj D) :
    Obj (A ⊕ₜ B) ≅ Obj (C ⊕ₜ D) :=
  sumIso Seed A B ≪≫ coprod.mapIso e f ≪≫ (sumIso Seed C D).symm

private noncomputable def productMapIso {A B C D : τ} (e : Obj A ≅ Obj C) (f : Obj B ≅ Obj D) :
    Obj (A ×ₜ B) ≅ Obj (C ×ₜ D) :=
  (whiskerRightFunctor Seed (Obj B)).mapIso e ≪≫ (whiskerLeftFunctor Seed (Obj C)).mapIso f

private noncomputable def productEmpty (A : τ) :
    Obj (A ×ₜ Silmaril.empty) ≅ Obj (Silmaril.empty : τ) :=
  (J).mapIso
    ((Classical.choice (Paper.StructurallyEmpty.initial (Φ := Φ)
      (.right (A := A) .empty))).uniqueUpToIso (Paper.TypeCategory.emptyIsInitial (Φ := Φ)))

private noncomputable def productIso
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    (l : UnitTree) : (r : UnitTree) → Obj (l.ty ×ₜ r.ty) ≅ Obj (l.product r).ty
  | .empty => productEmpty Seed l.ty
  | .unit => rightUnitIsoOfEta Seed (unit_eta_of_include Seed includeUnit) (Obj l.ty)
  | .sum r s =>
    (J).mapIso (Paper.RetainedCase.distributorIso l.ty r.ty s.ty) ≪≫
      sumMapIso Seed (productIso includeUnit l r) (productIso includeUnit l s)

noncomputable def stateIso
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L) :
    (t : StructuralState) → Obj t.ty ≅ Obj t.tree.ty
  | .empty => Iso.refl _
  | .unit => Iso.refl _
  | .sum l r => sumMapIso Seed (stateIso includeUnit l) (stateIso includeUnit r)
  | .product l r => productMapIso Seed (stateIso includeUnit l) (stateIso includeUnit r) ≪≫
      productIso Seed includeUnit l.tree r.tree

private theorem transport_batch {A D B : Q} (e : A ≅ D) (g h : D ⟶ B ⨿ D) :
    transportStep Seed e g ≫ coprod.desc coprod.inl (transportStep Seed e h) =
      transportStep Seed e (g ≫ coprod.desc coprod.inl h) := by
  have continuation : coprod.map (𝟙 B) e.inv ≫ coprod.desc coprod.inl (transportStep Seed e h) =
      coprod.desc coprod.inl h ≫ coprod.map (𝟙 B) e.inv := by
    apply coprod.hom_ext <;> simp [transportStep]
  simp only [transportStep, Category.assoc]
  rw [show e.hom ≫ h ≫ coprod.map (𝟙 B) e.inv = transportStep Seed e h from rfl, continuation]

private theorem iterate_transport {A D B : Q} (e : A ≅ D) (g : D ⟶ B ⨿ D) :
    iterateChosen Seed (transportStep Seed e g) = e.hom ≫ iterateChosen Seed g := by
  change iterateChosen Seed (e.hom ≫ (g ≫ coprod.map (𝟙 B) e.inv)) = _
  rw [iterateChosen_roll, Category.assoc, coprod.map_map, Category.id_comp,
    Iso.inv_hom_id, coprod.map_id_id, Category.comp_id]

theorem transport_triple {A D B : Q} (e : A ≅ D) (g : D ⟶ B ⨿ D) :
    triple (transportStep Seed e g) = transportStep Seed e (triple g) := by
  change transportStep Seed e g ≫ coprod.desc coprod.inl
    (transportStep Seed e g ≫ coprod.desc coprod.inl (transportStep Seed e g)) = _
  rw [transport_batch, transport_batch]

theorem triple_transport_iff {A D B : Q} (e : A ≅ D) (g : D ⟶ B ⨿ D) :
    iterateChosen Seed (triple (transportStep Seed e g)) = iterateChosen Seed (transportStep Seed e g) ↔
      iterateChosen Seed (triple g) = iterateChosen Seed g := by
  rw [transport_triple, iterate_transport, iterate_transport, cancel_epi]

theorem triple_step
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    (t : StructuralState) {B : Q} (g : Obj t.ty ⟶ B ⨿ Obj t.ty) :
    iterateChosen Seed (triple g) = iterateChosen Seed g := by
  let e := stateIso Seed includeUnit t
  let h := transportStep Seed e.symm g
  have recover : transportStep Seed e h = g := by
    simp only [transportStep, h, Iso.symm_hom, Iso.symm_inv, Category.assoc, coprod.map_map,
      Iso.hom_inv_id, coprod.map_id_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  rw [← recover, triple_transport_iff]
  exact triple_step_unit_tree Seed includeUnit t.tree h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTripling
