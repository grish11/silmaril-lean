module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.MultiNested.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiSyntax
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Boundary.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.ReplaceNewest.Thms

/-! # Exact comparison of a checked table with several selected nested rows -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiAdmission

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.MultiNested
open Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite (InnerPlan innerLayout)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

private def payloadType (A D : Ty Empty) : Option CaseTag → Ty Empty
  | none => A
  | some tag => tag.sumType A D

private abbrev wideTypes {m : Nat} (P : Fin m → Ty Empty) (chosen : Fin m → Option CaseTag)
    (D : Fin m → Ty Empty) :=
  fun i => payloadType (P i) (D i) (chosen i)

private abbrev labels {m : Nat} (P : Fin m → Ty Empty) (L : LCtx (Ty Empty)) := List.ofFn P ++ L

private theorem localAt {m : Nat} (P : Fin m → Ty Empty) (L : LCtx (Ty Empty)) (i : Fin m) :
    At (labels P L) i (P i) := by simp [At, labels, List.getElem?_append_left, i.isLt]

private theorem exitAt {m : Nat} (P : Fin m → Ty Empty) {L : LCtx (Ty Empty)} {i : Nat} {A : Ty Empty}
    (h : At L i A) : At (labels P L) (m+i) A := by
  simpa [At, labels, List.getElem?_append_right] using h

section Maps

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty Empty) V)

private noncomputable def payloadMap (A D : Ty Empty) (choice : Option CaseTag) :
    M.obj A ⟶ M.obj (payloadType A D choice) :=
  match choice with
  | none => 𝟙 _
  | some tag => tag.injection M A D

private noncomputable abbrev slot {m : Nat} (P : Fin m → Ty Empty) (chosen : Fin m → Option CaseTag)
    (D : Fin m → Ty Empty) : ∀ i, M.obj (P i) ⟶ M.obj (wideTypes P chosen D i) :=
  fun i => payloadMap M (P i) (D i) (chosen i)

/-- The checked transfer law is phrased on label injections, independently
of any row or iteration witness. -/
private structure Coordinates (out : RouteLayout Empty) {K W : LCtx (Ty Empty)}
    (post : labelObj M K ⟶ labelObj M W) : Prop where
  plain : ∀ i A, out[i]? = some (A, none) →
    ∃ (hl : At K i A) (hr : At W i A), labelInject M i hl ≫ post = labelInject M i hr
  tagged : ∀ i A tag, out[i]? = some (A, some tag) →
    ∃ (D : Ty Empty) (hl : At K i A) (hr : At W i (tag.sumType A D)),
      labelInject M i hl ≫ post = tag.injection M A D ≫ labelInject M i hr

private theorem local_plain {K : LCtx (Ty Empty)} {i : Nat} {A D : Ty Empty} {choice : Option CaseTag}
    (eq : choice = none) (h : At K i (payloadType A D choice)) (h' : At K i A) :
    payloadMap M A D choice ≫ labelInject M i h = labelInject M i h' := by
  subst choice
  exact Category.id_comp _

private theorem local_tagged {K : LCtx (Ty Empty)} {i : Nat} {A D : Ty Empty} {choice : Option CaseTag}
    {tag : CaseTag} (eq : choice = some tag) (h : At K i (payloadType A D choice))
    (h' : At K i (tag.sumType A D)) :
    payloadMap M A D choice ≫ labelInject M i h = tag.injection M A D ≫ labelInject M i h' := by
  subst choice
  rfl

private theorem coordinates {m : Nat} (P : Fin m → Ty Empty) (F : Fin m → Bool) (tags : Fin m → CaseTag)
    (D : Fin m → Ty Empty) (L : LCtx (Ty Empty)) :
    Coordinates M (layout P F L tags) (mapSlotBoundary M (slot M P (selection F tags) D) L) := by
  let chosen := selection F tags
  let W := wideTypes P chosen D
  let maps := slot M P chosen D
  have lookup {i : Nat} (hi : i < m) :
      (layout P F L tags)[i]? = some (P ⟨i, hi⟩, chosen ⟨i, hi⟩) := by
    simp [layout, chosen, List.getElem?_append_left, hi]
  have outward (i : Nat) : (layout P F L tags)[m + i]? = (L.map (fun A => (A, none)))[i]? := by
    simp [layout, List.getElem?_append_right]
  constructor
  · intro i A hit
    by_cases hi : i < m
    · let j : Fin m := ⟨i, hi⟩
      obtain ⟨same, choice⟩ := Prod.mk.inj (Option.some.inj ((lookup hi).symm.trans hit))
      change P j = A at same
      subst A
      have h : At (labels W L) j (W j) := localAt W L j
      change chosen j = none at choice
      have ht : At (labels W L) j (P j) := by
        change At (labels W L) j (payloadType (P j) (D j) (chosen j)) at h
        simpa only [choice, payloadType] using h
      exact ⟨localAt P L j, ht, (mapSlotBoundary_local M maps L j _ h).trans (local_plain M choice h ht)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i-m, by omega⟩
      rw [outward, List.getElem?_map] at hit
      obtain ⟨B, get, eq⟩ := Option.map_eq_some_iff.mp hit
      have h : At L j A := get.trans (congrArg (fun x : Ty Empty × Option CaseTag => some x.1) eq)
      exact ⟨exitAt P h, exitAt W h, mapSlotBoundary_exit M maps L h _ _⟩
  · intro i A tag hit
    by_cases hi : i < m
    · let j : Fin m := ⟨i, hi⟩
      obtain ⟨same, choice⟩ := Prod.mk.inj (Option.some.inj ((lookup hi).symm.trans hit))
      change P j = A at same
      subst A
      have h : At (labels W L) j (W j) := localAt W L j
      change chosen j = some tag at choice
      have ht : At (labels W L) j (tag.sumType (P j) (D j)) := by
        change At (labels W L) j (payloadType (P j) (D j) (chosen j)) at h
        simpa only [choice, payloadType] using h
      exact ⟨D j, localAt P L j, ht, (mapSlotBoundary_local M maps L j _ h).trans (local_tagged M choice h ht)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i-m, by omega⟩
      rw [outward, List.getElem?_map] at hit
      obtain ⟨_, _, eq⟩ := Option.map_eq_some_iff.mp hit
      cases eq

private theorem leaf_routes {out : RouteLayout Empty} {K W : LCtx (Ty Empty)}
    {post : labelObj M K ⟶ labelObj M W} (coord : Coordinates M out post)
    {Γ : VCtx (Ty Empty)} {r s : Region Φ} (checked : CheckedRoutes out Γ r s) :
    RegionConstructorRoutes M post (𝟙 _) Γ r s := by
  apply CheckedRoutes.toConstructorRoutes M checked
  · intro i A h
    obtain ⟨l, r, e⟩ := coord.plain i A h
    exact ⟨l, r, e.trans (Category.comp_id _).symm⟩
  · intro i A tag h
    obtain ⟨D, l, r, e⟩ := coord.tagged i A tag h
    exact ⟨D, l, r, by rw [Category.comp_id]; exact e⟩

private theorem inner_routes {out : RouteLayout Empty} {K W : LCtx (Ty Empty)}
    {post : labelObj M K ⟶ labelObj M W} (coord : Coordinates M out post) {n : Nat} (I : Fin n → Ty Empty)
    {Γ : VCtx (Ty Empty)} {r s : Region Φ} (checked : CheckedRoutes (innerLayout I out) Γ r s) :
    RegionConstructorRoutes M
      (labelAppendSplit M (List.ofFn I) K ≫ coprod.map post (𝟙 _))
      (labelAppendSplit M (List.ofFn I) W) Γ r s := by
  have liftExit {i : Nat} {B T : Ty Empty} (l : At K i B) (r : At W i T) (f : M.obj B ⟶ M.obj T)
      (h : labelInject M i l ≫ post = f ≫ labelInject M i r) :
      labelInject M (n+i) (exitAt I l) ≫ (labelAppendSplit M (List.ofFn I) K ≫ coprod.map post (𝟙 _)) =
        f ≫ labelInject M (n+i) (exitAt I r) ≫ labelAppendSplit M (List.ofFn I) W := by
    rw [← Category.assoc, labelAppendSplit_exit M I K l, Category.assoc,
      coprod.inl_map, ← Category.assoc, h, Category.assoc, labelAppendSplit_exit M I W r]
  have lookup {i : Nat} (h : i < n) : (innerLayout I out)[i]? = some (I ⟨i, h⟩, none) := by
    simp [innerLayout, List.getElem?_append_left, h]
  have outward (i : Nat) : (innerLayout I out)[n+i]? = out[i]? := by
    simp [innerLayout, List.getElem?_append_right]
  apply CheckedRoutes.toConstructorRoutes M checked
  · intro i B hit
    by_cases h : i < n
    · let j : Fin n := ⟨i, h⟩
      have eq : I j = B := congrArg Prod.fst (Option.some.inj ((lookup h).symm.trans hit))
      subst B
      have atLocal : At (List.ofFn I) j (I j) := by simp [At, j.isLt]
      refine ⟨localAt I K j, localAt I W j, ?_⟩
      erw [← Category.assoc, labelAppendSplit_local M I K j _ atLocal, Category.assoc,
        coprod.inr_map, Category.id_comp, labelAppendSplit_local M I W j _ atLocal]
    · obtain ⟨j, rfl⟩ : ∃ j, i = n+j := ⟨i-n, by omega⟩
      rw [outward] at hit
      obtain ⟨l, r, e⟩ := coord.plain j B hit
      have eq := liftExit l r (𝟙 _) (e.trans (Category.id_comp _).symm)
      rw [Category.id_comp] at eq
      exact ⟨exitAt I l, exitAt I r, eq⟩
  · intro i B tag hit
    by_cases h : i < n
    · rw [lookup h] at hit
      cases hit
    · obtain ⟨j, rfl⟩ : ∃ j, i = n+j := ⟨i-n, by omega⟩
      rw [outward] at hit
      obtain ⟨D, l, r, e⟩ := coord.tagged j B tag hit
      exact ⟨D, exitAt I l, exitAt I r, liftExit l r (tag.injection M B D) e⟩

end Maps


section Model

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

local notation "Env" => ctxObj M []

private theorem read_selected {k l : Nat} {keep : Fin (k + 1) ↪ Fin (l + 1)} {I : Fin (k + 1) → Ty Empty}
    {A : Ty Empty} {K : LCtx (Ty Empty)} {out : RouteLayout Empty} {body : Region Φ}
    {p : InnerPlan Φ (k + 1) (l + 1)} (checked : p.Valid keep I A out body)
    (roll : IterationRolling C) (len : out.length = K.length)
    {t : body.HasType [A] K} {f : J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M K)}
    (d : RegionDenotes J M t f) :
    CfgDenotesAt J M I p.table.entry (fun i => p.table.rows (keep i)) f := by
  have valid : p.table.Valid keep K.length body := len ▸ checked.table
  obtain ⟨S, _, slim⟩ := valid.readback J M roll d
  have eq : (fun i => S (keep i)) = I := by
    obtain ⟨ent, rows, _⟩ := slim
    exact checked.retained_types ent rows
  rw [eq] at slim
  exact slim

private theorem select_inner {A D : Ty Empty} {tag : CaseTag} {K : LCtx (Ty Empty)} {raw body : Region Φ}
    (prune : Region.PruneConstructorTests (raw.substVars (Tm.replaceNewest (tag.inject (.var 0)))) body)
    {t : raw.HasType [tag.sumType A D] K}
    {b : J.obj (ctxObj M [tag.sumType A D]) ⟶ J.obj (labelObj M K)}
    (w : RegionDenotes J M t b) :
    ∃ h : body.HasType [A] K, RegionDenotes J M h (J.map (Env ◁ tag.injection M A D) ≫ b) := by
  have value : ∃ h : (tag.inject (.var 0) : Tm Φ).HasType [A] (tag.sumType A D),
      Denotes J M h (J.map (snd Env (M.obj A) ≫ tag.injection M A D)) := by
    cases tag with
    | inl =>
        refine ⟨.inl (.var rfl), ?_⟩
        rw [J.map_comp]
        exact .inl (.var rfl)
    | inr =>
        refine ⟨.inr (.var rfl), ?_⟩
        rw [J.map_comp]
        exact .inr (.var rfl)
  obtain ⟨_, da⟩ := value
  obtain ⟨_, restricted⟩ := w.replaceNewest J M da
  exact prune.denotes J M restricted

private theorem inner_compare {k l : Nat} {keep : Fin (k + 1) ↪ Fin (l + 1)} {I : Fin (k + 1) → Ty Empty}
    {A : Ty Empty} {K W : LCtx (Ty Empty)} {out : RouteLayout Empty} {body : Region Φ}
    {post : labelObj M K ⟶ labelObj M W} {p : InnerPlan Φ (k + 1) (l + 1)}
    (coord : Coordinates M out post) (checked : p.Valid keep I A out body)
    (roll : IterationRolling C) (len : out.length = W.length)
    {tl : p.common.HasType [A] K} {tr : body.HasType [A] W}
    {f : J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M K)}
    {g : J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M W)}
    (left : RegionDenotes J M tl f) (right : RegionDenotes J M tr g) : g = f ≫ J.map post := by
  have shape : LabelsDetermined [A] K p.commonEntry p.commonRows I := by
    intro S he hr
    exact NestedCfgFiniteSyntax.aligned_inner false checked.entryRoute checked.rowRoutes he hr checked.paths
  exact CfgDenotesAt.postmap_of_routes J M I post
    (RegionConstructorRoutes.denotes J M (inner_routes M coord I (Region.checkRoutes?_sound checked.entryRoute)))
    (fun i => RegionConstructorRoutes.denotes J M
      (inner_routes M coord I (Region.checkRoutes?_sound (checked.rowRoutes i))))
    (left.cfg_readback_of_labels_determined J M shape) (read_selected J M checked roll len right)

private theorem row_anchor {m : Nat} {P S : Fin m → Ty Empty} {F : Fin m → Bool}
    {L : LCtx (Ty Empty)} {A B : Ty Empty} {form : Option CaseTag} {raw : Region Φ} {p : RowPlan Φ}
    {tags : Fin m → CaseTag}
    (roll : IterationRolling C) (row : p.Valid A (layout P F L tags) raw form) (fit : NestedCfgMultiSyntax.Fits A form B)
    {h : raw.HasType [B] (labels S L)} {f : J.obj (ctxObj M [B]) ⟶ J.obj (labelObj M (labels S L))}
    (d : RegionDenotes J M h f) (i : Fin m) (edge : p.targets i = true) :
    NestedCfgMultiSyntax.Fits (P i) (selection F tags i) (S i) := by
  cases row with
  | ordinary route =>
      change B = A at fit
      subst B
      exact NestedCfgMultiSyntax.target [] route h i (by simpa [RowPlan.targets] using edge)
  | @nested mask plan body tag prune checked =>
      obtain ⟨D, rfl⟩ := fit
      obtain ⟨_, selected⟩ := select_inner J M prune d
      have len : (layout P F L tags).length = (labels S L).length := by simp [layout, labels]
      obtain ⟨entry, rows, _⟩ := read_selected J M checked roll len selected
      rcases Bool.or_eq_true_iff.mp edge with throughEntry | throughRow
      · exact NestedCfgMultiSyntax.target (List.ofFn (fun j => (mask.types j, none))) checked.entryRoute
          (by simpa only [List.map_ofFn, Function.comp_def] using entry) i
          (by simpa only [List.length_ofFn] using throughEntry)
      · obtain ⟨j, _, next⟩ := List.any_eq_true.mp throughRow
        exact NestedCfgMultiSyntax.target (List.ofFn (fun j => (mask.types j, none))) (checked.rowRoutes j)
          (by simpa only [List.map_ofFn, Function.comp_def] using (rows j)) i
          (by simpa only [List.length_ofFn] using next)

private theorem row_eq {A D : Ty Empty} {form : Option CaseTag} {out : RouteLayout Empty}
    {K W : LCtx (Ty Empty)} {post : labelObj M K ⟶ labelObj M W}
    (roll : IterationRolling C) (len : out.length = W.length) (coord : Coordinates M out post)
    {raw : Region Φ} {p : RowPlan Φ} (checked : p.Valid A out raw form)
    {tl : p.commonRegion.HasType [A] K} {tw : raw.HasType [payloadType A D form] W}
    {f : J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M K)}
    {g : J.obj (ctxObj M [payloadType A D form]) ⟶ J.obj (labelObj M W)}
    (left : RegionDenotes J M tl f) (right : RegionDenotes J M tw g) :
    J.map (Env ◁ payloadMap M A D form) ≫ g = f ≫ J.map post := by
  cases checked with
  | ordinary route =>
      have eq := RegionConstructorRoutes.denotes J M (leaf_routes M coord (Region.checkRoutes?_sound route)) left right
      rw [J.map_id, Category.comp_id] at eq
      change J.map (Env ◁ 𝟙 (M.obj A)) ≫ g = _
      rw [MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]
      exact eq.symm
  | nested prune typed =>
      obtain ⟨_, selected⟩ := select_inner J M prune right
      exact inner_compare J M coord typed roll len left selected

variable {m n : Nat} {keep : Fin (m + 1) ↪ Fin (n + 1)} {P : Fin (m + 1) → Ty Empty}
  {F : Fin (m + 1) → Bool} {tags : Fin (m + 1) → CaseTag} {r : Region Φ} {L : LCtx (Ty Empty)} {p : Plan Φ (m + 1) (n + 1)}

local notation "Arrow" => J.obj Env ⟶ J.obj (labelObj M L)
local notation "ActualRows" => fun i => p.outer.rows (keep i)
local notation "CommonRows" => fun i => RowPlan.commonRegion (p.rows i)

private theorem align (roll : IterationRolling C) (ok : p.Valid keep P F r L tags) {S : Fin (m + 1) → Ty Empty}
    {f : Arrow} (d : CfgDenotesAt J M S p.outer.entry ActualRows f) :
    ∃ D : Fin (m + 1) → Ty Empty, S = wideTypes P (selection F tags) D := by
  obtain ⟨he, _, _, _, _, _, rows, _⟩ := d
  have initial (i : Fin (m + 1)) (hit : NestedAdmission.Finite.branchesTo i p.entry = true) :
      NestedCfgMultiSyntax.Fits (P i) (selection F tags i) (S i) :=
    NestedCfgMultiSyntax.target [] ok.entry he i (by simpa using hit)
  have advance (j i : Fin (m + 1)) (fit : NestedCfgMultiSyntax.Fits (P j) (selection F tags j) (S j))
      (edge : (p.rows j).targets i = true) :
      NestedCfgMultiSyntax.Fits (P i) (selection F tags i) (S i) :=
    row_anchor J M roll (ok.rows j) fit (rows j) i edge
  have tails (i : Fin (m + 1)) : ∃ D, S i = payloadType (P i) D (selection F tags i) := by
    have fit := NestedCfgFiniteSyntax.of_worklist initial advance (ok.anchors i)
    cases hi : selection F tags i with
    | none => exact ⟨.empty, by simpa [NestedCfgMultiSyntax.Fits, payloadType, hi] using fit⟩
    | some tag => simpa [NestedCfgMultiSyntax.Fits, payloadType, hi] using fit
  choose D eq using tails
  exact ⟨D, funext eq⟩

private theorem compare_reduced (roll : IterationRolling C) (ok : p.Valid keep P F r L tags) (D : Fin (m + 1) → Ty Empty)
    {f g : Arrow} (small : CfgDenotesAt J M P p.entry CommonRows f)
    (wide : CfgDenotesAt J M (wideTypes P (selection F tags) D) p.outer.entry ActualRows g) : f = g := by
  let post := mapSlotBoundary M (slot M P (selection F tags) D) L
  have coord := coordinates M P F tags D L
  have split_eq {Γ : VCtx (Ty Empty)}
      {a : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (labels P L))}
      {b : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (labels (wideTypes P (selection F tags) D) L))}
      (h : b = a ≫ J.map post) :
      b ≫ J.map (labelAppendSplit M (List.ofFn (wideTypes P (selection F tags) D)) L) =
        a ≫ J.map (labelAppendSplit M (List.ofFn P) L) ≫
          J.map (coprod.map (𝟙 _) (mapSlotLabels M (slot M P (selection F tags) D))) := by
    rw [h, Category.assoc, ← J.map_comp, mapSlotBoundary_split, J.map_comp]
  have mapped := CfgDenotesAt.postmap_of_slot_squares J M (slot M P (selection F tags) D) (𝟙 (labelObj M L))
    (fun _ _ _ _ dl dr => by
      have eq := RegionConstructorRoutes.denotes J M (leaf_routes M coord (Region.checkRoutes?_sound ok.entry)) dl dr
      rw [J.map_id, Category.comp_id] at eq
      exact split_eq eq.symm)
    (fun i _ _ a b dl dr => by
      have eq := row_eq J M (D := D i) roll (by simp [layout]) coord (ok.rows i) dl dr
      have component := split_eq (Γ := [P i]) (a := a) (b := J.map (Env ◁ slot M P (selection F tags) D i) ≫ b) eq
      rw [Category.assoc] at component
      exact component)
    small wide
  rwa [J.map_id, Category.comp_id, eq_comm] at mapped

private theorem common_type {out : RouteLayout Empty} {A : Ty Empty} {form : Option CaseTag} {raw : Region Φ}
    {row : RowPlan Φ} (ok : row.Valid A out raw form) : row.commonRegion.HasType [A] (out.map Prod.fst) := by
  cases ok with
  | ordinary h => exact (Region.checkRoutes?_sound h).hasType
  | @nested mask plan body tag prune checked =>
      have shape : (innerLayout mask.types out).map Prod.fst = List.ofFn mask.types ++ out.map Prod.fst := by
        simp [innerLayout, List.map_ofFn, Function.comp_def]
      exact .cfg mask.types (shape ▸ (Region.checkRoutes?_sound checked.entryRoute).hasType)
        (fun i => shape ▸ (Region.checkRoutes?_sound (checked.rowRoutes i)).hasType)

private theorem compare_checked (roll : IterationRolling C) (ok : p.Valid keep P F r L tags)
    {h h' : r.HasType [] L} {f g : Arrow}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g := by
  have shape : (layout P F L tags).map Prod.fst = labels P L := by
    simp [layout, labels, List.map_ofFn, Function.comp_def, List.map_map]
  obtain ⟨base, small⟩ := CfgDenotesAt.exists_of_typing J M P (L := L)
    (shape ▸ (Region.checkRoutes?_sound ok.entry).hasType) (fun i => shape ▸ common_type (ok.rows i))
  have agree {ht : r.HasType [] L} {b : Arrow} (w : RegionDenotes J M ht b) : base = b := by
    obtain ⟨_, _, trimmed⟩ := ok.outer.readback J M roll w
    obtain ⟨D, eq⟩ := align J M roll ok trimmed
    rw [eq] at trimmed
    exact compare_reduced J M roll ok D small trimmed
  exact (agree left).symm.trans (agree right)

theorem compare {masks : Fin (m + 1) → Option InnerMask}
    (roll : IterationRolling C) (ok : compare? keep P F r L masks tags = .certified)
    {h h' : r.HasType [] L} {f g : Arrow}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g := by
  cases found : check? keep P F r L masks tags with
  | none => simp [compare?, found] at ok
  | some p => exact compare_checked J M roll (NestedCfgMultiSyntax.checked found) left right

end Model

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiAdmission
