module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Thms

/-! # Native normalization of typed acyclic control before binary fold replay -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AcyclicReplyReadback

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent (Route)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies (Profile ReplyShape Row
  nativeUnit nativeBit Native unitObj dispatch dispatch_comp nativeRoute nativeTarget projectRow fold Seed)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic
open Paper.Extension.Singleton (iterateChosen)
open CfgEta.TypeCategory (returnRegion_typed caseValueBranches seqValueBranches)

universe u v

variable {Φ : Type} [Profile Φ]

local notation "U" => nativeUnit Φ
local notation "X" => unitObj Φ
local notation "N" => nativeShape Φ
local notation "I" => iterateChosen (Seed Φ)
local notation "drop" => Paper.TypeCategory.discardArrow (Φ := Φ)
  (Silmaril.coprod Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.UnitTy
    Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.UnitTy)

theorem region_typed {s t : ReplyShape} (p : Control Φ s t) :
    ValueBranches [s.ty] p.region [t.ty] := by
  induction p with
  | forward s => exact .br rfl (.var rfl)
  | inl l r => exact .br rfl (.inl (.var rfl))
  | inr l r => exact .br rfl (.inr (.var rfl))
  | call p => exact returnRegion_typed (.op (.var rfl))
  | let₁ producer sequel hp hs => exact seqValueBranches hp hs
  | case left right hl hr => exact caseValueBranches hl hr
  | empty t => exact returnRegion_typed (.abort (.var rfl))

set_option backward.isDefEq.respectTransparency false in
theorem native_region {s t : ReplyShape} (p : Control Φ s t) :
    p.native = Paper.TypeCategory.ofRegion (region_typed p) := by
  induction p with
  | forward s => exact (Paper.TypeCategory.ofRegion_id s.ty).symm
  | inl l r => exact Paper.TypeCategory.sumCofan_inl l.ty r.ty
  | inr l r => exact Paper.TypeCategory.sumCofan_inr l.ty r.ty
  | call p => rfl
  | let₁ producer sequel hp hs =>
      rw [Control.native, hp, hs]
      exact Paper.TypeCategory.ofRegion_comp _ _ (region_typed (.let₁ producer sequel))
  | case left right hl hr =>
      rw [Control.native, hl, hr]
      exact Paper.TypeCategory.coprod_desc_ofRegion _ _
  | empty t => exact Paper.TypeCategory.emptyHom_ext _ _

set_option backward.isDefEq.respectTransparency false in
private theorem case_left {l r : ReplyShape} {Y : Native Φ} (f : N l ⟶ Y) (g : N r ⟶ Y) :
    (Paper.TypeCategory.sumCofan l.ty r.ty).inl ≫
      (Paper.TypeCategory.sumIso l.ty r.ty).hom ≫ coprod.desc f g = f := by
  rw [← Category.assoc, Paper.TypeCategory.sumCofan_inl_sumIso_hom, coprod.inl_desc]

set_option backward.isDefEq.respectTransparency false in
private theorem case_right {l r : ReplyShape} {Y : Native Φ} (f : N l ⟶ Y) (g : N r ⟶ Y) :
    (Paper.TypeCategory.sumCofan l.ty r.ty).inr ≫
      (Paper.TypeCategory.sumIso l.ty r.ty).hom ≫ coprod.desc f g = g := by
  rw [← Category.assoc, Paper.TypeCategory.sumCofan_inr_sumIso_hom, coprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
theorem point_dispatch {Y : Native Φ} (s : ReplyShape) (k : s.Value → (U ⟶ Y)) (x : s.Value) :
    point s x ≫ dispatch s k = k x := by
  induction s with
  | empty => exact PEmpty.elim x
  | unit =>
      cases x
      exact Category.id_comp _
  | sum l r hl hr =>
      cases x with
      | inl x =>
          rw [point, dispatch, Category.assoc,
            case_left (l := l) (r := r), hl]
      | inr x =>
          rw [point, dispatch, Category.assoc,
            case_right (l := l) (r := r), hr]

set_option backward.isDefEq.respectTransparency false in
private theorem ext_points {Y : Native Φ} (s : ReplyShape) {f g : N s ⟶ Y}
    (eq : ∀ x : s.Value, point s x ≫ f = point s x ≫ g) : f = g := by
  induction s with
  | empty => exact Paper.TypeCategory.emptyHom_ext f g
  | unit => simpa only [point, Category.id_comp] using eq PUnit.unit
  | sum l r hl hr =>
      apply BinaryCofan.IsColimit.hom_ext (Paper.TypeCategory.sumCofanIsColimit l.ty r.ty)
      · apply hl
        intro x
        simpa only [point, Category.assoc] using eq (.inl x)
      · apply hr
        intro x
        simpa only [point, Category.assoc] using eq (.inr x)

private theorem dispatch_point (s : ReplyShape) : dispatch (Φ := Φ) s (point s) = 𝟙 (N s) := by
  apply ext_points s
  intro x
  rw [point_dispatch, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem render_then {α : Type u} {β : Type v} {Y Z : Native Φ} (r : Row Φ α)
    (leaf : α → (U ⟶ Y)) (next : α → Row Φ β) (out : β → (U ⟶ Z)) (f : Y ⟶ Z)
    (eq : ∀ x, leaf x ≫ f = (next x).render out) :
    r.render leaf ≫ f = (thenRow next r).render out := by
  induction r with
  | leaf a => exact eq a
  | call p k ih =>
      rw [Row.render, thenRow, Row.render, Category.assoc, dispatch_comp]
      simp only [ih]

set_option backward.isDefEq.respectTransparency false in
theorem control_point {s t : ReplyShape} (p : Control Φ s t) (x : s.Value) :
    point s x ≫ p.native = (p.readback x).render (point t) := by
  induction p with
  | forward s => exact Category.comp_id _
  | inl l r => rfl
  | inr l r => rfl
  | call p =>
      cases x
      rw [point, Control.native, Category.id_comp, Control.readback, Row.render]
      let f : U ⟶ N (Profile.reply p) := Paper.TypeCategory.primitiveReturn p
      change f = f ≫ dispatch (Profile.reply p) (point (Profile.reply p))
      rw [dispatch_point, Category.comp_id]
  | let₁ producer sequel hp hs =>
      rw [Control.native, ← Category.assoc, hp, Control.readback]
      exact render_then _ _ _ _ _ hs
  | @case l r t left right hl hr =>
      cases x with
      | inl x =>
          rw [point, Control.native, Control.readback, Category.assoc, case_left (l := l) (r := r)]
          exact hl x
      | inr x =>
          rw [point, Control.native, Control.readback, Category.assoc, case_right (l := l) (r := r)]
          exact hr x
  | empty t => exact PEmpty.elim x

theorem control_readback {s t : ReplyShape} (p : Control Φ s t) :
    p.native = dispatch s (fun x => (p.readback x).render (point t)) := by
  apply ext_points s
  intro x
  rw [point_dispatch, control_point]

set_option backward.isDefEq.respectTransparency false in
theorem program_readback {α : Type} {Y : Native Φ} (p : Program Φ α)
    (leaf : α → (U ⟶ Y)) : p.native leaf = p.readback.render leaf := by
  have h : p.body.native = (p.body.readback PUnit.unit).render (point p.output) := by
    simpa only [point, Category.id_comp] using control_point p.body PUnit.unit
  rw [Program.native, h, Program.readback]
  exact render_then _ _ (fun x => .leaf (p.jump x)) leaf _ (fun x => point_dispatch _ _ x)

theorem source_readback (l r : Program Φ Route) :
    sourceStep l r =
      Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.sourceStep
        l.readback r.readback := by
  simp only [sourceStep, program_readback,
    Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.sourceStep]

theorem target_readback (g : Program Φ Bool) :
    targetStep g =
      Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.targetStep
        g.readback := by
  simp only [targetStep, program_readback,
    Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.targetStep]

theorem square_iff_native (l r : Program Φ Route) (g : Program Φ Bool) :
    sourceStep l r ≫ coprod.map (𝟙 X) fold = fold ≫ targetStep g ↔
      l.native nativeRoute ≫ coprod.map (𝟙 U) drop = g.native nativeTarget ∧
      r.native nativeRoute ≫ coprod.map (𝟙 U) drop = g.native nativeTarget := by
  rw [source_readback, target_readback, program_readback, program_readback, program_readback]
  exact Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.square_iff_native_rows
    l.readback r.readback g.readback

theorem uniformity (l r : Program Φ Route) (g : Program Φ Bool)
    (square : sourceStep l r ≫ coprod.map (𝟙 X) fold = fold ≫ targetStep g) :
    I (sourceStep l r) = fold ≫ I (targetStep g) := by
  rw [source_readback, target_readback] at square ⊢
  exact Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.uniformity
    l.readback r.readback g.readback square

theorem example_codes :
    Example.left.readback.map Route.recurrent = Example.target.readback ∧
    Example.right.readback.map Route.recurrent = Example.target.readback := by
  constructor <;>
    simp only [Example.left, Example.right, Example.target, Program.readback,
      Example.producer, Example.targetProducer, Control.readback, thenRow, Row.map] <;>
    congr 1 <;> funext x <;> rcases x with x | x | x <;> rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AcyclicReplyReadback
