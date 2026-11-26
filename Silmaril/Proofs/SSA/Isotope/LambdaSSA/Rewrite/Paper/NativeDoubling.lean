module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.Alternating.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Thms

/-! # Native doubling via a constructor state map on an alternating loop -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NativeDoubling

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.Extension.Singleton (projection projectStep coprodComparison_inv_map
  iterateChosen_projectStep uniformity_of_constructor_square)
open Paper.Extension.Singleton.Alternating (projectStep_double)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => Paper.TypeCategory (τ := τ) Φ

private abbrev EmptySeed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop := fun _ _ _ _ => False
local notation "F" => projection (EmptySeed (τ := τ) (Φ := Φ))

private theorem reflect {D B : P} (f g : D ⟶ B) (eq : (F).map f = (F).map g) : f = g := by
  obtain ⟨_, hf, rfl⟩ := exists_ofRegion (A := (show τ from D)) (B := (show τ from B)) f
  obtain ⟨_, hg, rfl⟩ := exists_ofRegion (A := (show τ from D)) (B := (show τ from B)) g
  exact (ofRegion_eq_iff hf hg).2
    (((Paper.Extension.Singleton.ofRegion_eq_iff EmptySeed hf hg).1 eq).toPaper False.elim)

set_option backward.isDefEq.respectTransparency false

private theorem projected_row {D T B : P} (f : T ⟶ B ⨿ T) (g : D ⟶ B ⨿ D) (j k : D ⟶ T)
    (row : j ≫ f = g ≫ coprod.map (𝟙 B) k) :
    (F).map j ≫ projectStep EmptySeed f =
      projectStep EmptySeed g ≫ coprod.map (𝟙 ((F).obj B)) ((F).map k) := by
  let c := PreservesColimitPair.iso (F)
  change (F).map j ≫ (F).map f ≫ (c B T).inv =
    ((F).map g ≫ (c B D).inv) ≫ coprod.map (𝟙 ((F).obj B)) ((F).map k)
  rw [← (F).map_comp_assoc, row, (F).map_comp, Category.assoc, Category.assoc,
    ← (F).map_id B, coprodComparison_inv_map]

/-- A constructor map that agrees with the reset on both injections gives
native doubling if the step absorbs reset at input and on recurrence. -/
private theorem of_input_output_reset {D T B : P} (split : D ⨿ D ≅ T)
    (forget : T ⟶ D) (hForget : ConstructorReturn forget) (reset : D ⟶ D)
    (hl : (coprod.inl ≫ split.hom) ≫ forget = reset)
    (hr : (coprod.inr ≫ split.hom) ≫ forget = reset)
    (g : D ⟶ B ⨿ D) (input : reset ≫ g = g) (output : g ≫ coprod.map (𝟙 B) reset = g) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g := by
  let l : D ⟶ T := coprod.inl ≫ split.hom
  let r : D ⟶ T := coprod.inr ≫ split.hom
  let alt : T ⟶ B ⨿ T := split.inv ≫ coprod.desc
    (g ≫ coprod.map (𝟙 B) r) (g ≫ coprod.map (𝟙 B) l)
  have altLeft : l ≫ alt = g ≫ coprod.map (𝟙 B) r := by
    simp only [l, alt, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_desc]
  have altRight : r ≫ alt = g ≫ coprod.map (𝟙 B) l := by
    simp only [r, alt, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_desc]
  have square : alt ≫ coprod.map (𝟙 B) forget = forget ≫ g := by
    apply (cancel_epi split.hom).1
    apply coprod.hom_ext
    · simp only [← Category.assoc coprod.inl split.hom]
      change l ≫ (alt ≫ _) = l ≫ (forget ≫ g)
      rw [← Category.assoc l alt, altLeft, Category.assoc, coprod.map_map, Category.id_comp,
        show r ≫ forget = reset from hr, output, ← Category.assoc l forget, hl, input]
    · simp only [← Category.assoc coprod.inr split.hom]
      change r ≫ (alt ≫ _) = r ≫ (forget ≫ g)
      rw [← Category.assoc r alt, altRight, Category.assoc, coprod.map_map, Category.id_comp,
        show l ≫ forget = reset from hl, output, ← Category.assoc r forget, hr, input]
  let c := PreservesColimitPair.iso (F) D D
  let e := c ≪≫ (F).mapIso split
  have eLeft : coprod.inl ≫ e.hom = (F).map l := by
    change coprod.inl ≫ c.hom ≫ (F).map split.hom = _
    rw [← Category.assoc, PreservesColimitPair.iso_hom, inl_coprodComparison, ← (F).map_comp]
  have eRight : coprod.inr ≫ e.hom = (F).map r := by
    change coprod.inr ≫ c.hom ≫ (F).map split.hom = _
    rw [← Category.assoc, PreservesColimitPair.iso_hom, inr_coprodComparison, ← (F).map_comp]
  -- In the quotient, the actual fold of identities is needed. Use the
  -- unmodified tagged carrier and transport the native result arm by arm.
  have iterAlt := uniformity_of_constructor_square EmptySeed hForget alt g square
  have projLeft := projected_row alt g l r altLeft
  have projRight := projected_row alt g r l altRight
  have compare : Paper.Extension.Singleton.Alternating.step (projectStep EmptySeed g)
      (projectStep EmptySeed g) ≫ coprod.map (𝟙 ((F).obj B)) e.hom =
        e.hom ≫ projectStep EmptySeed alt := by
    apply coprod.hom_ext
    · rw [Paper.Extension.Singleton.Alternating.step, coprod.inl_desc_assoc, Category.assoc,
        coprod.map_map, Category.id_comp, eRight, ← Category.assoc, eLeft, projLeft]
    · rw [Paper.Extension.Singleton.Alternating.step, coprod.inr_desc_assoc, Category.assoc,
        coprod.map_map, Category.id_comp, eLeft, ← Category.assoc, eRight, projRight]
  have result := Paper.Extension.Singleton.uniformity_of_iso EmptySeed e _ _ compare
  rw [iterAlt, ← Category.assoc] at result
  have resetIter : (F).map reset ≫ Paper.Extension.Singleton.iterateChosen EmptySeed (projectStep EmptySeed g) =
      Paper.Extension.Singleton.iterateChosen EmptySeed (projectStep EmptySeed g) := by
    rw [iterateChosen_projectStep]
    rw [← (F).map_comp]
    congr 1
    have e := iterate_roll reset g
    rw [input, output] at e
    exact e.symm
  have folded :
      Paper.Extension.Singleton.iterateChosen EmptySeed
        (Paper.Extension.Singleton.Alternating.step (projectStep EmptySeed g) (projectStep EmptySeed g)) =
      coprod.desc (𝟙 ((F).obj D)) (𝟙 ((F).obj D)) ≫
        Paper.Extension.Singleton.iterateChosen EmptySeed (projectStep EmptySeed g) := by
    rw [result, Category.assoc]
    apply coprod.hom_ext
    · rw [← Category.assoc coprod.inl e.hom, eLeft, ← Category.assoc ((F).map l),
        ← (F).map_comp, show l ≫ forget = reset from hl, resetIter,
        coprod.inl_desc_assoc, Category.id_comp]
    · rw [← Category.assoc coprod.inr e.hom, eRight, ← Category.assoc ((F).map r),
        ← (F).map_comp, show r ≫ forget = reset from hr, resetIter,
        coprod.inr_desc_assoc, Category.id_comp]
  have doubled := (Paper.WithCaseReturns.StructuralValues.HiddenBit.alternating_fold_iff_double_of_seed
    EmptySeed (projectStep EmptySeed g)).1 folded
  rw [← projectStep_double EmptySeed, iterateChosen_projectStep, iterateChosen_projectStep] at doubled
  exact reflect _ _ doubled

theorem of_output_reset {D T B : P} (split : D ⨿ D ≅ T)
    (forget : T ⟶ D) (hForget : ConstructorReturn forget) (reset : D ⟶ D)
    (hl : (coprod.inl ≫ split.hom) ≫ forget = reset)
    (hr : (coprod.inr ≫ split.hom) ≫ forget = reset)
    (idem : reset ≫ reset = reset) (g : D ⟶ B ⨿ D) (output : g ≫ coprod.map (𝟙 B) reset = g) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g := by
  let started := reset ≫ g
  let two := g ≫ coprod.desc coprod.inl g
  have pre : reset ≫ started = started := by rw [← Category.assoc, idem]
  have post : started ≫ coprod.map (𝟙 B) reset = started := by rw [Category.assoc, output]
  have doublePrefix : started ≫ coprod.desc coprod.inl started = reset ≫ two := by
    have desc : coprod.map (𝟙 B) reset ≫ coprod.desc coprod.inl g =
        coprod.desc coprod.inl started := by
      rw [coprod.map_desc, Category.id_comp]
    change (reset ≫ g) ≫ coprod.desc coprod.inl started = reset ≫ (g ≫ coprod.desc coprod.inl g)
    rw [← desc, Category.assoc, ← Category.assoc g, output]
  have postTwo : two ≫ coprod.map (𝟙 B) reset = two := by
    change (g ≫ coprod.desc coprod.inl g) ≫ coprod.map (𝟙 B) reset = _
    rw [Category.assoc, coprod.desc_comp, coprod.inl_map, Category.id_comp, output]
  have eq := of_input_output_reset split forget hForget reset hl hr started pre post
  rw [doublePrefix, iterate_roll reset two, postTwo] at eq
  have starteded : reset ≫ iterate two = reset ≫ iterate g := by
    rw [eq]
    exact (iterate_roll reset g).trans (by rw [output])
  have withReset (k : D ⟶ B) :
      two ≫ coprod.desc (𝟙 B) (reset ≫ k) = two ≫ coprod.desc (𝟙 B) k := by
    have desc : coprod.map (𝟙 B) reset ≫ coprod.desc (𝟙 B) k =
        coprod.desc (𝟙 B) (reset ≫ k) := by
      rw [coprod.map_desc, Category.id_comp]
    rw [← desc, ← Category.assoc, postTwo]
  have unfoldTwo : two ≫ coprod.desc (𝟙 B) (iterate g) = iterate g := by
    change (g ≫ coprod.desc coprod.inl g) ≫ coprod.desc (𝟙 B) (iterate g) = _
    rw [Category.assoc, coprod.desc_comp, coprod.inl_desc, ← iterate_fixpoint g, ← iterate_fixpoint g]
  change iterate two = iterate g
  rw [iterate_fixpoint two, ← withReset (iterate two), starteded, withReset, unfoldTwo]

local notation "UnitTy" => (Silmaril.unit : τ)
local notation "U" => (ofType (Φ := Φ) UnitTy)
local notation "resetUnit" => discardArrow (Φ := Φ) UnitTy

theorem of_unit_output_reset {B : P} (g : U ⟶ B ⨿ U)
    (output : g ≫ coprod.map (𝟙 B) resetUnit = g) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g := by
  let forget := discardArrow (Φ := Φ) (Silmaril.coprod UnitTy UnitTy)
  have hForget : ConstructorReturn forget := ⟨.unit, .unit, rfl⟩
  let split := (sumIso (Φ := Φ) UnitTy UnitTy).symm
  have hl : (coprod.inl : U ⟶ U ⨿ U) ≫ split.hom = (sumCofan UnitTy UnitTy).inl := by
    change coprod.inl ≫ (sumIso UnitTy UnitTy).inv = _
    rw [← sumCofan_inl_sumIso_hom (Φ := Φ) UnitTy UnitTy, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hr : (coprod.inr : U ⟶ U ⨿ U) ≫ split.hom = (sumCofan UnitTy UnitTy).inr := by
    change coprod.inr ≫ (sumIso UnitTy UnitTy).inv = _
    rw [← sumCofan_inr_sumIso_hom (Φ := Φ) UnitTy UnitTy, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  apply of_output_reset split forget hForget resetUnit ?_ ?_ ?_ g output
  · rw [hl, sumCofan_inl]
    exact discard_comp_branchValue (.inl (.var rfl))
  · rw [hr, sumCofan_inr]
    exact discard_comp_branchValue (.inr (.var rfl))
  · exact discard_comp_branchValue (.unit (Γ := [UnitTy]))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NativeDoubling

end

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NativeDoubling.Example

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.Extension.Singleton (projection projectStep iterateChosen
  projection_map_desc_congr unit_eta_of_include)
open Paper.Extension.Singleton.Alternating (double_of_native step)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies
  (Profile Atom nativeUnit Row nativeTarget targetStep target_injective)

private inductive Op where
  | poll

local instance : Profile Op where
  reply _ := .sum .unit .unit

set_option backward.isDefEq.respectTransparency false

private abbrev unitType : Ty Atom := Silmaril.unit
local notation "X" => nativeUnit Op
local notation "reset" => discardArrow (τ := Ty Atom) (Φ := Op) unitType

-- A left reply requests another iteration. A right reply exits.
private def once : Row Op Bool :=
  .call .poll (fun | .inl _ => .leaf true | .inr _ => .leaf false)

private def twice : Row Op Bool :=
  .call .poll (fun | .inl _ => once | .inr _ => .leaf false)

private noncomputable abbrev g : X ⟶ X ⨿ X := once.render nativeTarget
private noncomputable abbrev g₂ : X ⟶ X ⨿ X := g ≫ coprod.desc coprod.inl g

private noncomputable def request : X ⟶ X ⨿ X :=
  primitiveReturn (τ := Ty Atom) Op.poll ≫ (sumIso (Φ := Op) unitType unitType).hom

private theorem single : g = request ≫ coprod.desc (reset ≫ coprod.inr) (reset ≫ coprod.inl) := by
  exact (Category.assoc _ _ _).symm

private theorem two_requests :
    twice.render nativeTarget = request ≫ coprod.desc g (reset ≫ coprod.inl) := by
  exact (Category.assoc _ _ _).symm

private theorem reset_output : g ≫ coprod.map (𝟙 X) reset = g := by
  rw [single, Category.assoc, coprod.desc_comp]
  congr 1
  have idem : reset ≫ reset = reset := discard_comp_branchValue (.unit (Γ := [unitType]))
  rw [Category.assoc, coprod.inr_map, ← Category.assoc, idem, Category.assoc, coprod.inl_map,
    Category.id_comp]

private theorem double_formula :
    g₂ = request ≫ coprod.desc (reset ≫ g) (reset ≫ coprod.inl) := by
  calc
    g₂ = (request ≫ coprod.desc (reset ≫ coprod.inr) (reset ≫ coprod.inl)) ≫
        coprod.desc coprod.inl g := congrArg (fun a => a ≫ coprod.desc coprod.inl g) single
    _ = _ := by
      rw [Category.assoc, coprod.desc_comp]
      simp only [Category.assoc, coprod.inr_desc, coprod.inl_desc]

private abbrev Observe :=
  Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Seed Op
local notation "F" => projection Observe

-- Readback of the existing finite-reply observer distinguishes one request
-- from two. Unit eta is used here for the observation of the second operand.
private theorem two_visible :
    projectStep Observe g₂ = targetStep twice := by
  have erase : (F).map reset = 𝟙 ((F).obj X) :=
    unit_eta_of_include Observe (fun e => .inl (.inl (.inr e)))
  change (F).map g₂ ≫ _ = (F).map (twice.render nativeTarget) ≫ _
  rw [double_formula, two_requests, (F).map_comp request, (F).map_comp request]
  have repeatArm : (F).map (reset ≫ g) = (F).map g := by
    rw [(F).map_comp, erase, Category.id_comp]
  rw [projection_map_desc_congr Observe repeatArm
    (rfl : (F).map (reset ≫ (coprod.inl : X ⟶ X ⨿ X)) = _)]

private def repeatPrefixLength : Row Op Bool → Nat
  | .leaf _ => 0
  | .call .poll next => repeatPrefixLength (next (.inl PUnit.unit)) + 1

example : g₂ ≠ g := by
  intro eq
  have rows : targetStep twice = targetStep once := two_visible.symm.trans
    (congrArg (projectStep Observe) eq)
  have lengths : 2 = 1 := congrArg repeatPrefixLength (target_injective rows)
  contradiction

example : iterate g₂ = iterate g := of_unit_output_reset g reset_output

private abbrev EntryLet := Paper.WithEntryLet.Step (τ := Ty Atom) (Φ := Op)

private theorem entryLet_double :
    iterateChosen EntryLet (projectStep EntryLet g ≫ coprod.desc coprod.inl
      (projectStep EntryLet g)) = iterateChosen EntryLet (projectStep EntryLet g) :=
  double_of_native EntryLet g (of_unit_output_reset g reset_output)

example : iterateChosen EntryLet (step (projectStep EntryLet g) (projectStep EntryLet g)) =
    coprod.desc (𝟙 _) (𝟙 _) ≫ iterateChosen EntryLet (projectStep EntryLet g) :=
  (Paper.WithCaseReturns.StructuralValues.HiddenBit.alternating_fold_iff_double_of_seed
    EntryLet (projectStep EntryLet g)).2 entryLet_double

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NativeDoubling.Example
