module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Restriction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.TakenTag.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.ReplaceNewest.Thms
import Mathlib.Tactic.IntervalCases

/-! # Equality of original exact witnesses for admitted nested CFGs -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmission

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.NestedAdmission
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

private abbrev U := unitTy
private abbrev Pair := pairTy
private abbrev tagged (D : Ty Empty) : Ty Empty := .coprod U D
private abbrev slots (A : Ty Empty) : Fin 1 → Ty Empty := fun _ => A
private abbrev labels (A : Ty Empty) := List.ofFn (slots A) ++ exits
private abbrev pathLabels (A : Ty Empty) := List.ofFn (slots U) ++ labels A
private def innerStates (live dead : Ty Empty) : Fin 2 → Ty Empty := Fin.cases live (fun _ => dead)

private abbrev entry : Region Φ := .br 0 .unit
private abbrev actualInnerEntry (loopTag : Bool) : Region Φ := (innerEntry loopTag).renameLabels labelIndex
private abbrev commonInner (p : Plan Φ) : Region Φ := .cfg (innerEntry false) 1 (fun _ => p.common)
private abbrev wideInner (p : Plan Φ) : Region Φ :=
  .cfg (p.entry.renameLabels labelIndex) 2 (fun i => (p.rows i).renameLabels labelIndex)

private theorem inner_family {S : Fin 2 → Ty Empty} {A : Ty Empty}
    (he : (actualInnerEntry (Φ := Φ) false).HasType [U] (List.ofFn S ++ labels A)) : S 0 = U := by
  change (Region.br 0 (.var 0) : Region Φ).HasType [U] (List.ofFn S ++ labels A) at he
  cases he with
  | br hit typed =>
      cases typed with
      | var hv =>
          have atHead : At (List.ofFn S ++ labels A) 0 (S 0) := by simp [At]
          exact (Option.some.inj (atHead.symm.trans hit)).trans (Option.some.inj hv).symm

private theorem inner_wide_family {S : Fin 2 → Ty Empty} {A : Ty Empty}
    (he : (actualInnerEntry (Φ := Φ) true).HasType [U] (List.ofFn S ++ labels A)) :
    ∃ D : Ty Empty, S 0 = tagged D := by
  change (Region.br 0 (.inl (.var 0)) : Region Φ).HasType [U] (List.ofFn S ++ labels A) at he
  cases he with
  | br hit typed =>
      have atHead : At (List.ofFn S ++ labels A) 0 (S 0) := by simp [At]
      have eq := Option.some.inj (atHead.symm.trans hit)
      cases typed with
      | inl value =>
          cases value with
          | var hv =>
              cases Option.some.inj hv
              exact ⟨_, eq⟩

private theorem innerStates_of_first {S : Fin 2 → Ty Empty} {A : Ty Empty} (h : S 0 = A) :
    ∃ D : Ty Empty, S = innerStates A D := by
  refine ⟨S 1, funext ?_⟩
  intro i
  refine Fin.cases h (Fin.cases rfl ?_) i
  intro j
  exact Fin.elim0 j

private theorem outer_family {S : Fin 1 → Ty Empty} {A : Ty Empty} {L : LCtx (Ty Empty)}
    {a : Tm Φ} (unique : TypeDetermined [] a A)
    (h : (Region.br 0 (.inl a)).HasType [] (List.ofFn S ++ L)) :
    ∃ D : Ty Empty, S = family (slots A) (some (slots D)) := by
  have atHead : At (List.ofFn S ++ L) 0 (S 0) := by simp [At]
  have head : ∃ D : Ty Empty, S 0 = .coprod A D := by
    cases h with
    | br hit typed =>
        have eq := Option.some.inj (atHead.symm.trans hit)
        cases typed with
        | inl value => exact ⟨_, (unique _ value) ▸ eq⟩
  obtain ⟨D, eq⟩ := head
  refine ⟨D, funext (Fin.cases eq ?_)⟩
  intro j
  exact Fin.elim0 j

section ValueMaps

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty Empty) V)

private noncomputable abbrev injectLeft (A D : Ty Empty) : M.obj A ⟶ M.obj (.coprod A D) :=
  coprod.inl ≫ (M.coprodIso A D).inv

private noncomputable abbrev inLeft (D : Ty Empty) := injectLeft M U D

private noncomputable abbrev post (D : Ty Empty) := mapLabelHead M exits (inLeft M D)

private theorem post_head (D : Ty Empty) :
    labelInject M 0 (rfl : At (labels U) 0 U) ≫ post M D =
      inLeft M D ≫ labelInject M 0 (rfl : At (labels (tagged D)) 0 (tagged D)) :=
  mapLabelHead_zero M exits (inLeft M D)

private theorem post_unit (D : Ty Empty) :
    labelInject M 1 (rfl : At (labels U) 1 U) ≫ post M D =
      labelInject M 1 (rfl : At (labels (tagged D)) 1 U) :=
  mapLabelHead_succ M exits (inLeft M D) (i := 0) rfl

private theorem post_pair (D : Ty Empty) :
    labelInject M 2 (rfl : At (labels U) 2 Pair) ≫ post M D =
      labelInject M 2 (rfl : At (labels (tagged D)) 2 Pair) :=
  mapLabelHead_succ M exits (inLeft M D) (i := 1) rfl

private noncomputable abbrev outerCut (A : Ty Empty) (L : LCtx (Ty Empty)) :=
  labelAppendSplit M (List.ofFn (slots A)) L

private noncomputable abbrev outerMap (A D : Ty Empty) (L : LCtx (Ty Empty)) :=
  coprod.map (𝟙 (labelObj M L)) (embedLabels M (slots A) (slots D))

@[reassoc] private theorem outerCut_head (A : Ty Empty) (L : LCtx (Ty Empty)) :
    labelInject M 0 (rfl : At (A :: L) 0 A) ≫ outerCut M A L =
      labelInject M 0 (rfl : At (List.ofFn (slots A)) 0 A) ≫ coprod.inr :=
  labelAppendSplit_local M (slots A) L 0 rfl rfl

@[reassoc] private theorem outerCut_exit (A : Ty Empty) (L : LCtx (Ty Empty)) {i : Nat} {T : Ty Empty}
    (hi : At L i T) :
    labelInject M (i + 1) (show At (A :: L) (i + 1) T from hi) ≫ outerCut M A L =
      labelInject M i hi ≫ coprod.inl := by
  have shifted : At (List.ofFn (slots A) ++ L) (i + 1) T := hi
  have route := labelAppendSplit_exit M (slots A) L (i := i) hi (by simpa only [Nat.add_comm 1 i] using shifted)
  simpa only [Nat.add_comm 1 i] using route

@[reassoc] private theorem embed_head {A : Ty Empty} (D : Ty Empty) :
    labelInject M 0 (rfl : At (List.ofFn (slots A)) 0 A) ≫ embedLabels M (slots A) (slots D) =
      injectLeft M A D ≫ labelInject M 0 (rfl : At (List.ofFn (slots (.coprod A D))) 0 (.coprod A D)) := by
  unfold embedLabels
  have conv : labelInject M 0 (rfl : At (List.ofFn (slots A)) 0 A) ≫
      labelObjToFinite M (slots A) = finiteLabelInject M (slots A) 0 :=
    labelObjToFinite_local M (slots A) 0 rfl
  erw [← Category.assoc, conv]
  exact Sigma.ι_comp_desc _ _

private theorem post_split (A D : Ty Empty) (L : LCtx (Ty Empty)) :
    mapLabelHead M L (injectLeft M A D) ≫ outerCut M (.coprod A D) L =
      outerCut M A L ≫ outerMap M A D L := by
  apply labelHom_ext M
  intro i T h
  cases i with
  | zero =>
      have eq : A = T := Option.some.inj h
      subst T
      simp only [mapLabelHead_zero_assoc, outerCut_head, outerCut_head_assoc, coprod.inr_map, embed_head_assoc]
      erw [Category.assoc]
      rfl
  | succ i =>
      have hi : At L i T := h
      simp only [mapLabelHead_succ_assoc M L (injectLeft M A D) hi, outerCut_exit M _ L hi,
        outerCut_exit_assoc M _ L hi, coprod.inl_map, Category.id_comp]
      rfl

private noncomputable abbrev innerCut (state outward : Ty Empty) :=
  labelAppendSplit M (List.ofFn (slots state)) (labels outward)

private noncomputable abbrev innerLeft (D : Ty Empty) {A : Ty Empty}
    (stateMap : labelObj M (List.ofFn (slots U)) ⟶ labelObj M (List.ofFn (slots A))) :=
  innerCut M U U ≫ coprod.map (post M D) stateMap

@[reassoc] private theorem innerCut_head (A B : Ty Empty) :
    labelInject M 0 (rfl : At (List.ofFn (slots A) ++ labels B) 0 A) ≫ innerCut M A B =
      labelInject M 0 (rfl : At (List.ofFn (slots A)) 0 A) ≫ coprod.inr :=
  labelAppendSplit_local M (slots A) (labels B) 0 rfl rfl

private theorem local_route (D : Ty Empty) :
    labelInject M 0 (rfl : At (pathLabels U) 0 U) ≫ innerLeft M D (𝟙 _) =
      labelInject M 0 (rfl : At (pathLabels (tagged D)) 0 U) ≫ innerCut M U (tagged D) := by
  simp only [innerCut_head, innerCut_head_assoc, coprod.inr_map, Category.id_comp]
  rfl

private theorem local_route_wide (D E : Ty Empty) :
    labelInject M 0 (rfl : At (pathLabels U) 0 U) ≫
        innerLeft M D (embedLabels M (slots U) (slots E)) =
      inLeft M E ≫
        labelInject M 0 (rfl : At (List.ofFn (slots (tagged E)) ++ labels (tagged D)) 0 (tagged E)) ≫
        innerCut M (tagged E) (tagged D) := by
  simp only [innerCut_head, innerCut_head_assoc, coprod.inr_map, embed_head_assoc, Category.assoc]
  rfl

private theorem exit_route (D : Ty Empty) {state : Ty Empty}
    (stateMap : labelObj M (List.ofFn (slots U)) ⟶ labelObj M (List.ofFn (slots state)))
    {i : Nat} {A B : Ty Empty}
    (hl : At (labels U) i A) (hr : At (labels (tagged D)) i B) (payload : M.obj A ⟶ M.obj B)
    (atExit : labelInject M i hl ≫ post M D = payload ≫ labelInject M i hr)
    (sl : At (pathLabels U) (1 + i) A)
    (sr : At (List.ofFn (slots state) ++ labels (tagged D)) (1 + i) B) :
    labelInject M (1 + i) sl ≫ innerLeft M D stateMap =
      payload ≫ labelInject M (1 + i) sr ≫ innerCut M state (tagged D) := by
  rw [← Category.assoc, labelAppendSplit_exit M (slots U) (labels U) hl, Category.assoc,
    coprod.inl_map, ← Category.assoc, atExit, Category.assoc,
    labelAppendSplit_exit M (slots state) (labels (tagged D)) hr]
  rfl

private abbrev liveTy (tag : Bool) (E : Ty Empty) := if tag then tagged E else U

private noncomputable def stateMap (tag : Bool) (E : Ty Empty) :
    labelObj M (List.ofFn (slots U)) ⟶ labelObj M (List.ofFn (slots (liveTy tag E))) :=
  match tag with
  | false => 𝟙 _
  | true => embedLabels M (slots U) (slots E)

private theorem checkedRoutes (D E : Ty Empty) (tag : Bool) {r s : Region Φ}
    (checked : CheckedRoutes (layout tag) [U, U] r s) :
    RegionConstructorRoutes M (innerLeft M D (stateMap M tag E))
      (innerCut M (liveTy tag E) (tagged D)) [U, U] r s := by
  apply CheckedRoutes.toConstructorRoutes M checked
  · intro i A hit
    have bound : i < 4 := (List.getElem?_eq_some_iff.mp hit).1
    interval_cases i
    · cases tag
      · have h : A = U := (congrArg Prod.fst (Option.some.inj hit)).symm
        subst A
        exact ⟨rfl, rfl, local_route M D⟩
      · simp [layout] at hit
    · simp [layout] at hit
    · have h : A = U := (congrArg Prod.fst (Option.some.inj hit)).symm
      subst A
      refine ⟨rfl, rfl, ?_⟩
      have eq := exit_route M D (stateMap M tag E) rfl rfl (𝟙 (M.obj U))
        (by rw [Category.id_comp, post_unit]) rfl rfl
      rw [Category.id_comp] at eq
      exact eq
    · have h : A = Pair := (congrArg Prod.fst (Option.some.inj hit)).symm
      subst A
      refine ⟨rfl, rfl, ?_⟩
      have eq := exit_route M D (stateMap M tag E) rfl rfl (𝟙 (M.obj Pair))
        (by rw [Category.id_comp, post_pair]) rfl rfl
      rw [Category.id_comp] at eq
      exact eq
  · intro i A choice hit
    have bound : i < 4 := (List.getElem?_eq_some_iff.mp hit).1
    cases choice
    case inr => interval_cases i <;> cases tag <;> simp [layout] at hit
    interval_cases i
    · cases tag
      · simp [layout] at hit
      · have h : A = U := (congrArg Prod.fst (Option.some.inj hit)).symm
        subst A
        exact ⟨E, rfl, rfl, local_route_wide M D E⟩
    · have h : A = U := (congrArg Prod.fst (Option.some.inj hit)).symm
      subst A
      exact ⟨D, rfl, rfl, exit_route M D (stateMap M tag E) rfl rfl (inLeft M D) (post_head M D) rfl rfl⟩
    · simp [layout] at hit
    · simp [layout] at hit

private theorem finite_checked_routes {m : Nat} (P : Fin m → Ty Empty) (L : LCtx (Ty Empty))
    (A D : Ty Empty) {Γ : VCtx (Ty Empty)} {r s : Region Φ}
    (checked : CheckedRoutes (Finite.layout P L A) Γ r s) :
    RegionConstructorRoutes M
      (labelAppendSplit M (List.ofFn P) (A :: L) ≫ coprod.map (mapLabelHead M L (injectLeft M A D)) (𝟙 _))
      (labelAppendSplit M (List.ofFn P) (.coprod A D :: L)) Γ r s := by
  have localAt (K : LCtx (Ty Empty)) (i : Fin m) : At (List.ofFn P ++ K) i (P i) := by
    simp [At, List.getElem?_append_left, i.isLt]
  have exitAt {K : LCtx (Ty Empty)} {i : Nat} {T : Ty Empty} (h : At K i T) :
      At (List.ofFn P ++ K) (m + i) T := by
    simpa [At, List.getElem?_append_right] using h
  have exitRoute {i : Nat} {B T : Ty Empty} (l : At (A :: L) i B) (r : At (.coprod A D :: L) i T)
      (v : M.obj B ⟶ M.obj T)
      (h : labelInject M i l ≫ mapLabelHead M L (injectLeft M A D) = v ≫ labelInject M i r) :
      labelInject M (m + i) (exitAt l) ≫
          (labelAppendSplit M (List.ofFn P) (A :: L) ≫ coprod.map (mapLabelHead M L (injectLeft M A D)) (𝟙 _)) =
        v ≫ labelInject M (m + i) (exitAt r) ≫ labelAppendSplit M (List.ofFn P) (.coprod A D :: L) := by
    rw [← Category.assoc, labelAppendSplit_exit M P (A :: L) l, Category.assoc, coprod.inl_map,
      ← Category.assoc, h, Category.assoc, labelAppendSplit_exit M P (.coprod A D :: L) r]
  have lookupLocal {i : Nat} (h : i < m) :
      (Finite.layout P L A)[i]? = some (P ⟨i, h⟩, none) := by
    simp [Finite.layout, List.getElem?_append_left, h]
  have lookupExit (i : Nat) :
      (Finite.layout P L A)[m + i]? = ((A, some .inl) :: L.map (fun T => (T, none)))[i]? := by
    simp [Finite.layout, List.getElem?_append_right]
  apply CheckedRoutes.toConstructorRoutes M checked
  · intro i B hit
    by_cases hi : i < m
    · have eq : P ⟨i, hi⟩ = B := congrArg Prod.fst (Option.some.inj ((lookupLocal hi).symm.trans hit))
      subst B
      let j : Fin m := ⟨i, hi⟩
      have atLocal : At (List.ofFn P) j (P j) := by simp [At, j.isLt]
      refine ⟨localAt _ j, localAt _ j, ?_⟩
      rw [← Category.assoc, labelAppendSplit_local M P _ j _ atLocal, Category.assoc,
        coprod.inr_map, Category.id_comp, labelAppendSplit_local M P _ j _ atLocal]
    · obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i - m, by omega⟩
      rw [lookupExit] at hit
      cases j with
      | zero => simp at hit
      | succ j =>
          simp only [List.getElem?_cons_succ, List.getElem?_map] at hit
          obtain ⟨T, get, eq⟩ := Option.map_eq_some_iff.mp hit
          have h : At L j B := get.trans (congrArg (fun x : Ty Empty × Option CaseTag => some x.1) eq)
          refine ⟨exitAt (show At (A :: L) (j + 1) B from h),
            exitAt (show At (.coprod A D :: L) (j + 1) B from h), ?_⟩
          simpa only [Category.id_comp] using exitRoute (i := j + 1) h h (𝟙 (M.obj B))
            (by rw [Category.id_comp, mapLabelHead_succ M L (injectLeft M A D) h])
  · intro i B tag hit
    by_cases hi : i < m
    · rw [lookupLocal hi] at hit
      cases hit
    · obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i - m, by omega⟩
      rw [lookupExit] at hit
      cases j with
      | zero =>
          obtain ⟨rfl, tagEq⟩ := Prod.mk.inj (Option.some.inj hit)
          cases Option.some.inj tagEq
          exact ⟨D, exitAt rfl, exitAt rfl, exitRoute (i := 0) rfl rfl (injectLeft M A D)
            (mapLabelHead_zero M L (injectLeft M A D))⟩
      | succ j =>
          simp only [List.getElem?_cons_succ, List.getElem?_map] at hit
          obtain ⟨_, _, eq⟩ := Option.map_eq_some_iff.mp hit
          cases eq

end ValueMaps

section Model

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

private theorem guard_denotes {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)} {A D : Ty Empty}
    {raw body : Region Φ}
    (prune : Region.PruneConstructorTests (raw.substVars (Tm.replaceNewest (.inl (.var 0)))) body)
    {t : raw.HasType ((.coprod A D) :: Γ) L}
    {f : J.obj (ctxObj M ((.coprod A D) :: Γ)) ⟶ J.obj (labelObj M L)}
    (wide : RegionDenotes J M t f) :
    ∃ h : body.HasType (A :: Γ) L,
      RegionDenotes J M h (J.map (ctxObj M Γ ◁ injectLeft M A D) ≫ f) := by
  have arg : Denotes J M (.inl (.var rfl) (B := D) :
      (Tm.inl (.var 0) : Tm Φ).HasType (A :: Γ) ((.coprod A D)))
      (J.map (snd (ctxObj M Γ) (M.obj A) ≫ injectLeft M A D)) := by
    rw [J.map_comp]
    exact .inl (.var rfl)
  obtain ⟨_, restricted⟩ := wide.replaceNewest J M arg
  exact prune.denotes J M restricted

private theorem commonShape (p : Plan Φ) :
    LabelsDetermined [U] (labels U) (innerEntry false) (fun _ => p.common) (slots U) := by
  intro S he _
  have head : S 0 = U := by
    change (Region.br 0 (.var 0) : Region Φ).HasType [U] (List.ofFn S ++ labels U) at he
    cases he with
    | br hit typed =>
        cases typed with
        | var hv =>
            have atHead : At (List.ofFn S ++ labels U) 0 (S 0) := by simp [At]
            exact (Option.some.inj (atHead.symm.trans hit)).trans (Option.some.inj hv).symm
  funext i
  exact Fin.cases head (fun j => Fin.elim0 j) i

private theorem inner_compare (roll : IterationRolling C) {r : Region Φ} {p : Plan Φ} (admitted : p.Valid r)
    (D : Ty Empty) {t : (commonInner p).HasType [U] (labels U)}
    {t' : (wideInner p).HasType [U] (labels (tagged D))}
    {f : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels U))}
    {g : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels (tagged D)))}
    (left : RegionDenotes J M t f) (right : RegionDenotes J M t' g) : g = f ≫ J.map (post M D) := by
  have small := left.cfg_readback_of_labels_determined J M (commonShape p)
  obtain ⟨T, wide⟩ := right.cfg_readback J M
  cases tagEq : p.taggedInner with
  | false =>
      have wideShape : ∃ dead, T = innerStates U dead := by
        obtain ⟨he, _⟩ := wide
        exact innerStates_of_first (inner_family (by simpa only [admitted.entry, tagEq] using he))
      obtain ⟨dead, rfl⟩ := wideShape
      have slim := CfgDenotesAt.restrict J M keep (innerStates U dead) (L := labels (tagged D))
        roll admitted.entryScope admitted.rowScope wide
      have ent : RegionConstructorRoutes M (innerLeft M D (𝟙 _)) (innerCut M U (tagged D))
          [U] (innerEntry false) p.entry := by
        rw [admitted.entry, tagEq]
        exact .br rfl rfl (.var rfl) (local_route M D)
      have hr : CheckedRoutes (layout false) [U, U] p.common (p.rows 0) := by
        have eq : p.rows 0 = p.selected := by simpa only [tagEq, Bool.false_eq_true, ite_false] using admitted.row
        simpa only [tagEq, eq] using admitted.routes
      have row := checkedRoutes M D .empty false hr
      exact CfgDenotesAt.postmap_of_routes J M (slots U) (post M D)
        (ent.denotes J) (fun _ => row.denotes J) small slim
  | true =>
      have wideShape : ∃ E dead, T = innerStates (tagged E) dead := by
        obtain ⟨he, _⟩ := wide
        obtain ⟨E, live⟩ := inner_wide_family (by simpa only [admitted.entry, tagEq] using he)
        obtain ⟨dead, shape⟩ := innerStates_of_first live
        exact ⟨E, dead, shape⟩
      obtain ⟨E, dead, rfl⟩ := wideShape
      have slim := CfgDenotesAt.restrict J M keep (innerStates (tagged E) dead) (L := labels (tagged D))
        roll admitted.entryScope admitted.rowScope wide
      have ent : RegionConstructorRoutes M (innerLeft M D (stateMap M true E))
          (innerCut M (tagged E) (tagged D)) [U] (innerEntry false) p.entry := by
        rw [admitted.entry, tagEq]
        exact .inl rfl rfl (.var rfl) (local_route_wide M D E)
      have hr : CheckedRoutes (layout true) [U, U] p.common p.selected := by simpa only [tagEq] using admitted.routes
      have row := checkedRoutes M D E true hr
      refine CfgDenotesAt.postmap_of_taken_tag_squares J M (slots E) (post M D) ?_ ?_ small slim
      · intro _ _ _ _ de dw
        have eq := RegionConstructorRoutes.denotes J M ent de dw
        rw [J.map_comp] at eq
        exact eq.symm
      · intro _ _ _ _ _ ds dw
        have prune : Region.PruneConstructorTests ((p.rows 0).substVars (Tm.replaceNewest (.inl (.var 0))))
            p.selected := by simpa only [tagEq, ite_true] using admitted.row
        obtain ⟨_, restricted⟩ := guard_denotes J M (Γ := [U]) (D := E) prune dw
        have eq := RegionConstructorRoutes.denotes J M row ds restricted
        rw [J.map_comp, Category.assoc] at eq
        exact eq.symm

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

private theorem compare_with_common {A : Ty Empty} {L : LCtx (Ty Empty)} {a : Tm Φ}
    {r outer common selected : Region Φ}
    (unique : TypeDetermined [] a A) (arg : DeterminedTerm [] a A)
    (root : r = .cfg (.br 0 (.inl a)) 1 (fun _ => outer))
    (prune : Region.PruneConstructorTests (outer.substVars (Tm.replaceNewest (.inl (.var 0)))) selected)
    (inner : ∀ (D : Ty Empty) {t : common.HasType [A] (A :: L)}
      {t' : selected.HasType [A] (.coprod A D :: L)}
      {f : J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M (A :: L))}
      {g : J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M (.coprod A D :: L))},
      RegionDenotes J M t f → RegionDenotes J M t' g → g = f ≫ J.map (mapLabelHead M L (injectLeft M A D)))
    {f g : J.obj (ctxObj M []) ⟶ J.obj (labelObj M L)}
    (small : CfgDenotesAt J M (slots A) (.br 0 a) (fun _ => common) f)
    {ht : r.HasType [] L} (wide : RegionDenotes J M ht g) : f = g := by
  obtain ⟨ht', d⟩ : ∃ ht' : (Region.cfg (.br 0 (.inl a)) 1 (fun _ => outer)).HasType [] L,
      RegionDenotes J M ht' g := by rw [← root]; exact ⟨_, wide⟩
  obtain ⟨S, actual⟩ := d.cfg_readback J M
  have shape : ∃ D : Ty Empty, S = family (slots A) (some (slots D)) := by
    obtain ⟨typed, _⟩ := actual
    exact outer_family unique typed
  obtain ⟨D, rfl⟩ := shape
  refine CfgDenotesAt.eq_of_taken_tag_squares J M (slots D) ?_ ?_ small actual
  · intro _ _ _ _ de dw
    have route : RegionConstructorRoutes M (outerCut M A L ≫ outerMap M A D L)
        (outerCut M (.coprod A D) L) [] (.br 0 a) (.br 0 (.inl a)) := by
      refine RegionConstructorRoutes.inl (i := 0) (j := 0) (A := A) (D := D) rfl rfl arg ?_
      rw [← post_split]
      simpa only [injectLeft, Category.assoc] using
        mapLabelHead_zero_assoc M L (injectLeft M A D) (outerCut M (.coprod A D) L)
    have eq := RegionConstructorRoutes.denotes J M route de dw
    rw [J.map_comp] at eq
    exact eq.symm
  · intro _ _ _ _ _ ds dw
    obtain ⟨_, selected⟩ := guard_denotes J M prune dw
    have innerEq := inner D ds selected
    have factor : mapLabelHead M L (injectLeft M A D) ≫
        labelAppendSplit M (List.ofFn (family (slots A) (some (slots D)))) L =
          outerCut M A L ≫ outerMap M A D L := post_split M A D L
    rw [← Category.assoc, innerEq, Category.assoc, ← J.map_comp, factor, J.map_comp]

theorem compare (roll : IterationRolling C) {r : Region Φ} {p : Plan Φ} (admitted : p.Valid r)
    {t t' : r.HasType [] exits} {f g : Arrow}
    (left : RegionDenotes J M t f) (right : RegionDenotes J M t' g) : f = g := by
  have row : p.common.HasType [U, U] (pathLabels U) := admitted.routes.hasType
  have inner : (commonInner p).HasType [U] (labels U) :=
    .cfg (slots U) (.br rfl (.var rfl)) (fun _ => row)
  obtain ⟨_, small⟩ := CfgDenotesAt.exists_of_typing J M (slots U)
    (.br rfl .unit : (entry (Φ := Φ)).HasType [] (labels U)) (fun _ => inner)
  have unique : TypeDetermined [] (.unit : Tm Φ) U := fun _ h => by cases h; rfl
  exact (compare_with_common J M unique .unit admitted.root admitted.outer
    (inner_compare J M roll admitted) small left).symm.trans
    (compare_with_common J M unique .unit admitted.root admitted.outer
      (inner_compare J M roll admitted) small right)

section Finite

theorem finite_inner_compare {k n : Nat} {keep : Fin (k + 1) ↪ Fin (n + 1)}
    {P : Fin (k + 1) → Ty Empty} {r : Region Φ} {p : Finite.Plan Φ (k + 1) (n + 1)}
    {L : LCtx (Ty Empty)} (roll : IterationRolling C) (admitted : p.Valid keep P r L) (D : Ty Empty)
    {t : p.commonInner.HasType [p.payload] (p.payload :: L)}
    {t' : (p.selectedInner keep).HasType [p.payload] (.coprod p.payload D :: L)}
    {f : J.obj (ctxObj M [p.payload]) ⟶ J.obj (labelObj M (p.payload :: L))}
    {g : J.obj (ctxObj M [p.payload]) ⟶ J.obj (labelObj M (.coprod p.payload D :: L))}
    (left : RegionDenotes J M t f) (right : RegionDenotes J M t' g) :
    g = f ≫ J.map (mapLabelHead M L (coprod.inl ≫ (M.coprodIso p.payload D).inv)) := by
  have commonShape : LabelsDetermined [p.payload] (p.payload :: L) p.commonEntry p.commonRows P := by
    intro S he hr
    exact NestedCfgFiniteSyntax.aligned false admitted.entryRoute admitted.rowRoutes he hr admitted.paths
  have small := left.cfg_readback_of_labels_determined J M commonShape
  obtain ⟨S, actual⟩ := right.cfg_readback J M
  have trimmed := CfgDenotesAt.restrict J M keep S (L := .coprod p.payload D :: L) roll
    admitted.entryScope admitted.rowScope actual
  have eq : (fun i => S (keep i)) = P := by
    obtain ⟨he, hr, _⟩ := trimmed
    exact NestedCfgFiniteSyntax.aligned true admitted.entryRoute admitted.rowRoutes he hr admitted.paths
  rw [eq] at trimmed
  exact CfgDenotesAt.postmap_of_routes J M P (mapLabelHead M L (injectLeft M p.payload D))
    ((finite_checked_routes M P L p.payload D (Region.checkRoutes?_sound admitted.entryRoute)).denotes J)
    (fun i => (finite_checked_routes M P L p.payload D
      (Region.checkRoutes?_sound (admitted.rowRoutes i))).denotes J)
    small trimmed

theorem compare_finite {k n : Nat} {keep : Fin (k + 1) ↪ Fin (n + 1)}
    {P : Fin (k + 1) → Ty Empty} {r : Region Φ} {p : Finite.Plan Φ (k + 1) (n + 1)}
    {L : LCtx (Ty Empty)} (roll : IterationRolling C) (admitted : p.Valid keep P r L)
    {t t' : r.HasType [] L} {f g : J.obj (ctxObj M []) ⟶ J.obj (labelObj M L)}
    (left : RegionDenotes J M t f) (right : RegionDenotes J M t' g) : f = g := by
  have shape : (Finite.layout P L p.payload).map Prod.fst = List.ofFn P ++ p.payload :: L := by
    simp [Finite.layout, List.map_ofFn, Function.comp_def, List.map_map]
  have inner : p.commonInner.HasType [p.payload] (p.payload :: L) :=
    .cfg P (shape ▸ (Region.checkRoutes?_sound admitted.entryRoute).hasType)
      (fun i => shape ▸ (Region.checkRoutes?_sound (admitted.rowRoutes i)).hasType)
  obtain ⟨init, unique, arg⟩ := Tm.synthRouteType?_sound admitted.initializerType
  obtain ⟨_, small⟩ := CfgDenotesAt.exists_of_typing J M (slots p.payload)
    (.br rfl init : (Region.br 0 p.initializer).HasType [] (List.ofFn (slots p.payload) ++ L)) (fun _ => inner)
  exact (compare_with_common J M unique arg admitted.root admitted.outer
    (finite_inner_compare J M roll admitted) small left).symm.trans
    (compare_with_common J M unique arg admitted.root admitted.outer
      (finite_inner_compare J M roll admitted) small right)

end Finite

end Model

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmission
