module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms

/-! # Restrict the original dispatcher along a retained label family -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgTrim

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ : Type u} {m n : Nat} (keep : Fin m ↪ Fin n) (S : Fin n → τ)
  (L : LCtx τ)

local notation "P" => (fun i => S (keep i))

private theorem localAt {k : Nat} (R : Fin k → τ) (K : LCtx τ) (i : Fin k) :
    At (List.ofFn R ++ K) i (R i) := by
  have bound : i.val < (List.ofFn R).length := by simp
  simp [At, List.getElem?_append_left bound]

private theorem exitAt {k : Nat} (R : Fin k → τ) {K : LCtx τ} {i : Nat} {A : τ} :
    At (List.ofFn R ++ K) (k + i) A ↔ At K i A := by
  have bound : (List.ofFn R).length ≤ k + i := by simp
  simp only [At, List.getElem?_append_right bound, List.length_ofFn, Nat.add_sub_cancel_left]

private theorem index_local (i : Fin m) : retainLabelIndex keep i = keep i := by
  simp [retainLabelIndex, i.isLt]

private theorem index_exit (i : Nat) : retainLabelIndex keep (m + i) = n + i := by
  have h : ¬ m + i < m := by omega
  simp [retainLabelIndex, h]

theorem ren : Ren (List.ofFn P ++ L) (List.ofFn S ++ L) (retainLabelIndex keep) := by
  intro i A h
  by_cases hit : i < m
  · let j : Fin m := ⟨i, hit⟩
    have eq := Option.some.inj (h.symm.trans (localAt P L j))
    subst A
    have moved : retainLabelIndex keep i = keep j := index_local keep j
    simpa only [moved] using localAt S L (keep j)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hit)
    rw [index_exit]
    exact (exitAt S).mpr ((exitAt P).mp h)

private theorem renLocal : Ren (List.ofFn P) (List.ofFn S) (retainLabelIndex keep) := by
  simpa only [List.append_nil] using ren keep S []

section Maps

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [TypeFormers τ] (M : TypeModel τ V)

private noncomputable def includeFinite : finiteLabelObj M P ⟶ finiteLabelObj M S :=
  Sigma.desc fun i => finiteLabelInject M S (keep i)

@[reassoc] private theorem finite_include (i : Fin m) :
    finiteLabelInject M P i ≫ includeFinite keep S M = finiteLabelInject M S (keep i) :=
  Sigma.ι_comp_desc _ _

private theorem ren_to_finite :
    labelMap M (renLocal keep S) ≫ labelObjToFinite M S =
      labelObjToFinite M P ≫ includeFinite keep S M := by
  apply labelHom_ext M
  intro i A h
  have bound : i < m := by simpa only [List.length_ofFn] using (List.getElem?_eq_some_iff.mp h).1
  let j : Fin m := ⟨i, bound⟩
  have hj : At (List.ofFn P) j (P j) := by simp [At]
  have eq := Option.some.inj (h.symm.trans hj)
  subst A
  have target : retainLabelIndex keep i = keep j := index_local keep j
  have hs : At (List.ofFn S) (keep j) (S (keep j)) := by simp [At]
  have moved : labelInject M i h ≫ labelMap M (renLocal keep S) =
      labelInject M (keep j) hs := by
    simpa only [target] using labelInject_labelMap M (renLocal keep S) h
  rw [← Category.assoc, moved, labelObjToFinite_local, ← Category.assoc,
    labelObjToFinite_local M P j hj, finite_include]

private theorem ren_split :
    labelMap M (ren keep S L) ≫ labelAppendSplit M (List.ofFn S) L =
      labelAppendSplit M (List.ofFn P) L ≫ coprod.map (𝟙 (labelObj M L)) (labelMap M (renLocal keep S)) := by
  apply labelHom_ext M
  intro i A h
  by_cases hit : i < m
  · let j : Fin m := ⟨i, hit⟩
    have eq := Option.some.inj (h.symm.trans (localAt P L j))
    subst A
    have target : retainLabelIndex keep i = keep j := index_local keep j
    have moved : labelInject M i h ≫ labelMap M (ren keep S L) =
        labelInject M (keep j) (localAt S L (keep j)) := by
      simpa only [target] using labelInject_labelMap M (ren keep S L) h
    have hj : At (List.ofFn P) j (P j) := by simp [At]
    have hs : At (List.ofFn S) (keep j) (P j) := by simp [At]
    have localMove : labelInject M j hj ≫ labelMap M (renLocal keep S) =
        labelInject M (keep j) hs := by
      simpa only [index_local keep j] using labelInject_labelMap M (renLocal keep S) hj
    rw [← Category.assoc, moved, labelAppendSplit_local M S L (keep j) _ hs,
      ← Category.assoc, labelAppendSplit_local M P L j _ hj, Category.assoc, coprod.inr_map,
      ← Category.assoc, localMove]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hit)
    have hj := (exitAt P).mp h
    have moved : labelInject M (m + j) h ≫ labelMap M (ren keep S L) =
        labelInject M (n + j) ((exitAt S).mpr hj) := by
      simpa only [index_exit] using labelInject_labelMap M (ren keep S L) h
    rw [← Category.assoc, moved, labelAppendSplit_exit M S L hj, ← Category.assoc,
      labelAppendSplit_exit M P L hj, Category.assoc, coprod.inl_map, Category.id_comp]

end Maps

section Dispatch

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [TypeFormers τ] (M : TypeModel τ V) {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem restrict {k l : Nat} (keep : Fin (k + 1) ↪ Fin (l + 1)) (S : Fin (l + 1) → τ)
    {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ} {rows : Fin (l + 1) → Region Φ}
    (roll : IterationRolling C) (entryScope : entry.LabelsBound (k + 1 + L.length))
    (rowsScope : ∀ i, (rows i).LabelsBound (k + 1 + L.length))
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (w : CfgDenotesAt J M S (entry.renameLabels (retainLabelIndex keep))
      (fun i => (rows i).renameLabels (retainLabelIndex keep)) f) :
    CfgDenotesAt J M (fun i => S (keep i)) entry (fun i => rows (keep i)) f := by
  let retained : Fin (k + 1) → τ := fun i => S (keep i)
  let E := ctxObj M Γ
  let B := labelObj M L
  let cut := labelAppendSplit M (List.ofFn retained) L
  let cutLarge := labelAppendSplit M (List.ofFn S) L
  let inc := labelMap M (renLocal keep S)
  let hf := includeFinite keep S M
  let route := J.map (coprod.map (𝟙 B) inc)
  let hρ := ren keep S L
  obtain ⟨_, _, fe, fb, large, de, db, dc, rfl⟩ := w
  obtain ⟨he', fe', de', entry_eq⟩ := de.of_renameLabels J M
    (by simpa only [List.length_append, List.length_ofFn] using entryScope) hρ
  have selected (i : Fin (l + 1)) := (db i).of_renameLabels J M
    (by simpa only [List.length_append, List.length_ofFn] using rowsScope i) hρ
  choose hb' fb' db' block_eq using selected
  obtain ⟨small, smallRows⟩ := collective_exists J M k Γ retained (labelObj M (List.ofFn retained ++ L))
    (fun i => fb' (keep i))
  obtain ⟨mid, midRows⟩ := collective_exists J M l Γ S (B ⨿ labelObj M (List.ofFn retained))
    (fun i => fb' i ≫ J.map cut)
  have transfer {X : C} {a : X ⟶ J.obj (labelObj M (List.ofFn retained ++ L))} :
      a ≫ J.map (labelMap M hρ) ≫ J.map cutLarge = a ≫ J.map cut ≫ route := by
    dsimp only [hρ, cutLarge, cut, route, inc]
    simp only [← J.map_comp, ren_split]
    rfl
  have rows_eq : large ≫ J.map cutLarge = mid ≫ route := by
    apply collective_ext J M l Γ S
    intro i
    rw [← Category.assoc _ large, dc.restrict i, ← Category.assoc _ mid, midRows i, block_eq i]
    simp only [Category.assoc, transfer]
  have before : J.map (E ◁ hf) ≫ mid = small ≫ J.map cut := by
    apply collective_ext J M k Γ retained
    intro i
    rw [MonoidalCategory.id_tensorHom, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      finite_include, ← MonoidalCategory.id_tensorHom, midRows (keep i)]
    have selected := smallRows i
    rw [MonoidalCategory.id_tensorHom] at selected
    rw [← Category.assoc _ small, selected]
  let middle := J.map (E ◁ labelObjToFinite M S) ≫ mid
  have aligned : J.map (E ◁ inc) ≫ middle =
      J.map (E ◁ labelObjToFinite M retained) ≫ small ≫ J.map cut := by
    unfold middle
    rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, ren_to_finite,
      MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc, before]
  have computed := cfgDispatch_of_state_factorization J roll inc (fe' ≫ J.map cut) middle
  rw [aligned] at computed
  unfold middle at computed
  refine ⟨he', fun i => hb' (keep i), fe', fun i => fb' (keep i), small, de',
    fun i => db' (keep i), ⟨smallRows⟩, ?_⟩
  have entry_fact : fe ≫ J.map (labelAppendSplit M (List.ofFn S) L) = fe' ≫ J.map cut ≫ route := by
    rw [entry_eq, Category.assoc]
    exact transfer
  unfold cfgDispatchArrow
  simp only [MonoidalCategory.id_tensorHom]
  rw [entry_fact, ← Category.assoc _ large, Category.assoc, rows_eq]
  simpa only [Category.assoc] using computed.symm

end Dispatch

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgTrim
