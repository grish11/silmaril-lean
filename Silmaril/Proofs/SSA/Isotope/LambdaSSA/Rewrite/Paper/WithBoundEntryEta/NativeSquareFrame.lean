module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NativeSquareFrame

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open WithBoundEntryEta.NativeFrame
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion sumCofan sumIso)
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A B D E I X Y L R : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "State" => Silmaril.coprod X Y

set_option backward.isDefEq.respectTransparency false

theorem letCaseTable_guarded {n : Nat} {init disc : Tm Φ} {left right : Region Φ}
    {rows : Fin n → Region Φ} (labels : Fin n → τ)
    (hi : Tm.HasType [D] init I) (hd : Tm.HasType [I, D] disc (Silmaril.coprod L R))
    (hl : ValueBranches [L, I, D] left (List.ofFn labels ++ [E]))
    (hr : ValueBranches [R, I, D] right (List.ofFn labels ++ [E]))
    (hb : ∀ j, ValueBranches [labels j, D] (rows j) (List.ofFn labels ++ [E])) :
    ValueBranches [D] (letCaseTable init disc left right rows) [E] :=   .let₁ hi (.cfg labels (.case hd hl hr) (fun j => (hb j).renameVars ((Ren.wk [D] I).lift (labels j))))

theorem repeating_guarded {work : Region Φ} {reply : Tm Φ}
    (hw : ValueBranches [D] work [E]) (hb : Tm.BranchValue [E] reply D) :
    ValueBranches [D] (repeating work reply) [Silmaril.coprod B D] :=   CfgEta.TypeCategory.seqValueBranches hw (.br rfl (.inr hb))

theorem specialize_guarded {r : Region Φ} {state : Tm Φ}
    (ha : Tm.BranchValue [A] state D) (hr : ValueBranches [D] r [B]) :
    ValueBranches [A] (r.substVars (Tm.singleSubst state ∘ lift Nat.succ)) [B] := by
  apply hr.substVars
  intro i C hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ i => simp [At] at hi

theorem repeating_composite {work : Region Φ} {reply : Tm Φ}
    (hw : ValueBranches [D] work [E]) (hb : Tm.BranchValue [E] reply D) :
    ofRegion (repeating_guarded (B := B) hw hb) ≫ (sumIso B D).hom =
      ofRegion hw ≫ ofRegion (.br (ℓ := 0) rfl hb) ≫ coprod.inr := by
  let tail : ValueBranches [E] (.br 0 (.inr reply)) [Silmaril.coprod B D] := .br rfl (.inr hb)
  have leg : ofRegion (.br (ℓ := 0) rfl hb) ≫ (sumCofan B D).inr = ofRegion tail := by
    rw [Paper.TypeCategory.sumCofan_inr]
    rfl
  rw [← Paper.TypeCategory.ofRegion_comp hw tail (repeating_guarded (B := B) hw hb), ← leg]
  simp

theorem linear_composite {work : Region Φ} {state reply : Tm Φ}
    (hw : ValueBranches [D] work [E]) (ha : Tm.BranchValue [A] state D)
    (hb : Tm.BranchValue [E] reply D) (next : Obj E ⟶ Obj A)
    (recurs : next ≫ ofRegion (.br (ℓ := 0) rfl ha) = ofRegion (.br (ℓ := 0) rfl hb)) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    linear (B := B) h (ofRegion hw) next ≫ coprod.map (𝟙 (Obj B)) h =
      ofRegion (specialize_guarded ha (repeating_guarded (B := B) hw hb)) ≫ (sumIso B D).hom := by
  dsimp only
  rw [← WithEntryLet.ofRegion_comp_constructor ha (repeating_guarded (B := B) hw hb)
    (specialize_guarded ha (repeating_guarded (B := B) hw hb)), Category.assoc, repeating_composite (B := B) hw hb]
  unfold linear
  simp only [Category.assoc, coprod.inr_map]
  rw [← Category.assoc next, recurs]

theorem split_post (h : Obj State ⟶ Obj D) (work : Obj D ⟶ Obj E)
    (nextLeft nextRight : Obj E ⟶ Obj State) (reply : Obj E ⟶ Obj D)
    (leftRecurs : nextLeft ≫ h = reply) (rightRecurs : nextRight ≫ h = reply) :
    split (B := B) h work nextLeft nextRight ≫ coprod.map (𝟙 (Obj B)) h =
      h ≫ work ≫ reply ≫ coprod.inr := by
  let tail : Obj D ⟶ Obj B ⨿ Obj D := work ≫ reply ≫ coprod.inr
  let l : Obj X ⟶ Obj State := (sumCofan X Y).inl
  let r : Obj Y ⟶ Obj State := (sumCofan X Y).inr
  have il : l ≫ (sumIso X Y).hom = coprod.inl := Paper.TypeCategory.sumCofan_inl_sumIso_hom X Y
  have ir : r ≫ (sumIso X Y).hom = coprod.inr := Paper.TypeCategory.sumCofan_inr_sumIso_hom X Y
  have collapse : coprod.desc (l ≫ h) (r ≫ h) = (sumIso X Y).inv ≫ h := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc, ← il, Category.assoc, Iso.hom_inv_id_assoc]
    · rw [coprod.inr_desc, ← ir, Category.assoc, Iso.hom_inv_id_assoc]
  have partition : (sumIso X Y).hom ≫ coprod.desc (l ≫ h) (r ≫ h) = h := by
    rw [collapse, Iso.hom_inv_id_assoc]
  unfold split
  rw [Category.assoc, coprod.desc_comp]
  simp only [Category.assoc, coprod.inr_map]
  rw [← Category.assoc nextLeft, leftRecurs, ← Category.assoc nextRight, rightRecurs]
  change _ = h ≫ tail
  have left : (sumCofan X Y).inl ≫ h ≫ tail = ((sumCofan X Y).inl ≫ h) ≫ tail :=
    (Category.assoc _ _ _).symm
  have right : (sumCofan X Y).inr ≫ h ≫ tail = ((sumCofan X Y).inr ≫ h) ≫ tail :=
    (Category.assoc _ _ _).symm
  rw [left, right, ← coprod.desc_comp, ← Category.assoc, partition]

theorem split_composite {work : Region Φ} {state reply : Tm Φ}
    (hw : ValueBranches [D] work [E]) (ha : Tm.BranchValue [State] state D)
    (hb : Tm.BranchValue [E] reply D) (nextLeft nextRight : Obj E ⟶ Obj State)
    (leftRecurs : nextLeft ≫ ofRegion (.br (ℓ := 0) rfl ha) = ofRegion (.br (ℓ := 0) rfl hb))
    (rightRecurs : nextRight ≫ ofRegion (.br (ℓ := 0) rfl ha) = ofRegion (.br (ℓ := 0) rfl hb)) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    split (B := B) h (ofRegion hw) nextLeft nextRight ≫ coprod.map (𝟙 (Obj B)) h =
      ofRegion (specialize_guarded ha (repeating_guarded (B := B) hw hb)) ≫ (sumIso B D).hom := by
  dsimp only
  rw [← WithEntryLet.ofRegion_comp_constructor ha (repeating_guarded (B := B) hw hb)
    (specialize_guarded ha (repeating_guarded (B := B) hw hb)), Category.assoc, repeating_composite (B := B) hw hb]
  exact split_post _ _ nextLeft nextRight _ leftRecurs rightRecurs

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NativeSquareFrame
