module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Mixed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMixedSyntax
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.ReplaceNewest.Thms

/-! # Assemble the exact outer square from mixed written admission -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMixedAdmission

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.Mixed
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

private abbrev labels {q : Nat} (A : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty)) :=
  List.ofFn (stateTypes A Q) ++ L

private theorem labels_eq {q : Nat} (A : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty)) :
    labels A Q L = A :: (List.ofFn Q ++ L) := by
  change List.ofFn (stateTypes A Q) ++ L = A :: (List.ofFn Q ++ L)
  rw [List.ofFn_succ]
  rfl

private theorem localAt {m : Nat} (S : Fin m → Ty Empty) (L : LCtx (Ty Empty)) (i : Fin m) :
    At (List.ofFn S ++ L) i (S i) := by simp [At, List.getElem?_append_left, i.isLt]

private theorem localOnly {m : Nat} (S : Fin m → Ty Empty) (i : Fin m) :
    At (List.ofFn S) i (S i) := by simp [At, i.isLt]

section Maps

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty Empty) V)

private noncomputable abbrev injectLeft (A D : Ty Empty) : M.obj A ⟶ M.obj (.coprod A D) :=
  coprod.inl ≫ (M.coprodIso A D).inv

private noncomputable def slot {q : Nat} (A D : Ty Empty) (Q : Fin q → Ty Empty) (i : Fin (q + 1)) :
    M.obj (stateTypes A Q i) ⟶ M.obj (stateTypes (.coprod A D) Q i) :=
  Fin.cases (injectLeft M A D) (fun j => 𝟙 (M.obj (Q j))) i

private noncomputable abbrev cut {q : Nat} (A : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty)) :=
  labelAppendSplit M (List.ofFn (stateTypes A Q)) L

private noncomputable abbrev stepPost {q : Nat} (A D : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty)) :=
  coprod.map (𝟙 (labelObj M L)) (mapSlotLabels M (slot M A D Q))

private noncomputable def post {q : Nat} (A D : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty)) :
    labelObj M (labels A Q L) ⟶ labelObj M (labels (.coprod A D) Q L) :=
  eqToHom (congrArg (labelObj M) (labels_eq A Q L)) ≫
    mapLabelHead M (List.ofFn Q ++ L) (injectLeft M A D) ≫
      eqToHom (congrArg (labelObj M) (labels_eq (.coprod A D) Q L).symm)

@[reassoc] private theorem inject_cast {K K' : LCtx (Ty Empty)} (e : K = K') {i : Nat} {T : Ty Empty}
    (h : At K i T) : labelInject M i h ≫ eqToHom (congrArg (labelObj M) e) = labelInject M i (e ▸ h) := by
  cases e
  exact Category.comp_id _

private theorem post_zero {q : Nat} (A D : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty)) :
    labelInject M 0 (localAt (stateTypes A Q) L 0) ≫ post M A D Q L =
      injectLeft M A D ≫ labelInject M 0 (localAt (stateTypes (.coprod A D) Q) L 0) := by
  rw [post, inject_cast_assoc M (labels_eq A Q L), mapLabelHead_zero_assoc,
    inject_cast M (labels_eq (.coprod A D) Q L).symm]

private theorem post_nonzero {q : Nat} (A D : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty))
    {i : Nat} {T : Ty Empty} (nz : i ≠ 0) (hl : At (labels A Q L) i T)
    (hr : At (labels (.coprod A D) Q L) i T) :
    labelInject M i hl ≫ post M A D Q L = labelInject M i hr := by
  cases i with
  | zero => exact (nz rfl).elim
  | succ i =>
      have shifted : At (A :: (List.ofFn Q ++ L)) (i + 1) T := (labels_eq A Q L) ▸ hl
      have h : At (List.ofFn Q ++ L) i T := shifted
      rw [post, inject_cast_assoc M (labels_eq A Q L), mapLabelHead_succ_assoc M _ _ h,
        inject_cast M (labels_eq (.coprod A D) Q L).symm]

private theorem post_local {q : Nat} (A D : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty))
    (j : Fin (q + 1)) :
    labelInject M j (localAt (stateTypes A Q) L j) ≫ post M A D Q L =
      slot M A D Q j ≫ labelInject M j (localAt (stateTypes (.coprod A D) Q) L j) := by
  refine Fin.cases (post_zero M A D Q L) (fun i => ?_) j
  have eq := post_nonzero M A D Q L (i := i.succ.val) (by simp)
    (localAt (stateTypes A Q) L i.succ) (localAt (stateTypes (.coprod A D) Q) L i.succ)
  exact eq.trans (Category.id_comp _).symm

private theorem post_cut {q : Nat} (A D : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty)) :
    post M A D Q L ≫ cut M (.coprod A D) Q L = cut M A Q L ≫ stepPost M A D Q L := by
  apply labelHom_ext M
  intro i T hit
  by_cases h : i < q + 1
  · let j : Fin (q + 1) := ⟨i, h⟩
    have eq : stateTypes A Q j = T := Option.some.inj ((localAt (stateTypes A Q) L j).symm.trans hit)
    subst T
    change labelInject M j (localAt (stateTypes A Q) L j) ≫ _ = _
    have left := labelAppendSplit_local M (stateTypes A Q) L j
      (localAt (stateTypes A Q) L j) (localOnly (stateTypes A Q) j)
    have right := labelAppendSplit_local M (stateTypes (.coprod A D) Q) L j
      (localAt (stateTypes (.coprod A D) Q) L j) (localOnly (stateTypes (.coprod A D) Q) j)
    calc
      _ = slot M A D Q j ≫
          labelInject M j (localAt (stateTypes (.coprod A D) Q) L j) ≫ cut M (.coprod A D) Q L := by
        rw [← Category.assoc, post_local, Category.assoc]
      _ = labelInject M j (localOnly (stateTypes A Q) j) ≫ mapSlotLabels M (slot M A D Q) ≫ coprod.inr := by
        rw [right]
        exact (mapSlotLabels_inject_assoc M (slot M A D Q) j
          (localOnly (stateTypes A Q) j) (localOnly (stateTypes (.coprod A D) Q) j) coprod.inr).symm
      _ = _ := by
        symm
        change labelInject M j (localAt (stateTypes A Q) L j) ≫ cut M A Q L ≫ stepPost M A D Q L = _
        rw [← Category.assoc, left, Category.assoc, coprod.inr_map]
  · obtain ⟨j, rfl⟩ : ∃ j, i = q + 1 + j := ⟨i - (q + 1), by omega⟩
    have exit : At L j T := by
      simpa [At, List.getElem?_append_right] using hit
    have ht : At (labels (.coprod A D) Q L) (q + 1 + j) T := by
      simpa [At, List.getElem?_append_right] using exit
    rw [← Category.assoc, post_nonzero M A D Q L (by omega) hit ht,
      labelAppendSplit_exit M (stateTypes (.coprod A D) Q) L exit ht,
      ← Category.assoc, labelAppendSplit_exit M (stateTypes A Q) L exit hit,
      Category.assoc, coprod.inl_map, Category.id_comp]

private theorem checked_routes {q : Nat} (A D : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty))
    {Γ : VCtx (Ty Empty)} {r s : Region Φ}
    (checked : CheckedRoutes (layout A (List.ofFn Q ++ L)) Γ r s) :
    RegionConstructorRoutes M (post M A D Q L) (𝟙 _) Γ r s := by
  apply CheckedRoutes.toConstructorRoutes M checked
  · intro i T hit
    cases i with
    | zero => simp [layout] at hit
    | succ i =>
        simp only [layout, List.getElem?_cons_succ, List.getElem?_map] at hit
        obtain ⟨U, get, eq⟩ := Option.map_eq_some_iff.mp hit
        have ht : At (List.ofFn Q ++ L) i T := get.trans (congrArg (fun x : Ty Empty × Option CaseTag => some x.1) eq)
        have hl : At (labels A Q L) (i + 1) T := (labels_eq A Q L).symm ▸ ht
        have hr : At (labels (.coprod A D) Q L) (i + 1) T := (labels_eq (.coprod A D) Q L).symm ▸ ht
        exact ⟨hl, hr, (post_nonzero M A D Q L (by simp) hl hr).trans (Category.comp_id _).symm⟩
  · intro i T tag hit
    cases i with
    | zero =>
        obtain ⟨rfl, tagEq⟩ := Prod.mk.inj (Option.some.inj hit)
        cases Option.some.inj tagEq
        refine ⟨D, localAt (stateTypes A Q) L 0, localAt (stateTypes (.coprod A D) Q) L 0, ?_⟩
        rw [Category.comp_id]
        exact post_zero M A D Q L
    | succ i =>
        simp only [layout, List.getElem?_cons_succ, List.getElem?_map] at hit
        obtain ⟨_, _, eq⟩ := Option.map_eq_some_iff.mp hit
        cases eq

private theorem append_cut {C : Type u₂} [Category.{v₂} C] (J : V ⥤ C) {q : Nat}
    {A D : Ty Empty} {Q : Fin q → Ty Empty} {L : LCtx (Ty Empty)}
    {Γ : VCtx (Ty Empty)} {a : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (labels A Q L))}
    {b : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (labels (.coprod A D) Q L))}
    (eq : b = a ≫ J.map (post M A D Q L)) :
    b ≫ J.map (cut M (.coprod A D) Q L) = a ≫ J.map (cut M A Q L) ≫ J.map (stepPost M A D Q L) := by
  rw [eq, Category.assoc, ← J.map_comp, post_cut, J.map_comp]

private theorem uncast_postmap {C : Type u₂} [Category.{v₂} C] (J : V ⥤ C)
    {Γ K K' W W' : List (Ty Empty)} (e : K = K') (e' : W = W')
    {a : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)}
    {b : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M W)} {out : labelObj M K' ⟶ labelObj M W'}
    (h : b ≫ J.map (eqToHom (congrArg (labelObj M) e')) =
      (a ≫ J.map (eqToHom (congrArg (labelObj M) e))) ≫ J.map out) :
    b = a ≫ J.map (eqToHom (congrArg (labelObj M) e) ≫ out ≫ eqToHom (congrArg (labelObj M) e'.symm)) := by
  cases e
  cases e'
  simpa using h

end Maps

section Model

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

variable {q o k n : Nat} {outerKeep : Fin (q + 1) ↪ Fin (o + 1)}
  {innerKeep : Fin (k + 1) ↪ Fin (n + 1)} {P : Fin (k + 1) → Ty Empty} {Q : Fin q → Ty Empty}
  {r : Region Φ} {L : LCtx (Ty Empty)} {p : Plan Φ q (o + 1) (k + 1) (n + 1)}

local notation "Payload" => p.inner.payload
local notation "Env" => ctxObj M []
local notation "Arrow" => J.obj Env ⟶ J.obj (labelObj M L)
local notation "LiveRows" => fun i => p.outer.rows (outerKeep i)

private theorem cast_denotes {Γ K K' : List (Ty Empty)} (e : K = K') {s : Region Φ}
    {t : s.HasType Γ K} {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)} (d : RegionDenotes J M t f) :
    ∃ t' : s.HasType Γ K', RegionDenotes J M t' (f ≫ J.map (eqToHom (congrArg (labelObj M) e))) := by
  cases e
  simpa using (show ∃ t' : s.HasType Γ K, RegionDenotes J M t' f from ⟨t, d⟩)

private theorem select_inner (ok : p.Valid outerKeep innerKeep P Q r L) (D : Ty Empty)
    {K : LCtx (Ty Empty)} {t : (p.outer.rows (outerKeep 0)).HasType [.coprod Payload D] K}
    {b : J.obj (ctxObj M [.coprod Payload D]) ⟶ J.obj (labelObj M K)} (w : RegionDenotes J M t b) :
    ∃ h : (p.inner.selectedInner innerKeep).HasType [Payload] K,
      RegionDenotes J M h (J.map (Env ◁ injectLeft M Payload D) ≫ b) := by
  have da : Denotes J M (.inl (.var rfl) (B := D) : (Tm.inl (.var 0) : Tm Φ).HasType [Payload] (.coprod Payload D))
      (J.map (snd Env (M.obj Payload) ≫ injectLeft M Payload D)) := by
    rw [J.map_comp]
    exact .inl (.var rfl)
  obtain ⟨_, restricted⟩ := w.replaceNewest J M da
  have prune : Region.PruneConstructorTests
      ((p.outer.rows (outerKeep 0)).substVars (Tm.replaceNewest (.inl (.var 0))))
      (p.inner.selectedInner innerKeep) := by
    rw [(NestedCfgMixedSyntax.shell_endpoints ok).2]
    exact ok.inner.outer
  exact prune.denotes J M restricted

private theorem align (ok : p.Valid outerKeep innerKeep P Q r L) {S : Fin (q + 1) → Ty Empty}
    {f : Arrow} (roll : IterationRolling C) (w : CfgDenotesAt J M S p.outer.entry LiveRows f) :
    ∃ D : Ty Empty, S = stateTypes (.coprod Payload D) Q := by
  obtain ⟨he, hr, _, b, _, _, rows, _⟩ := w
  have typed : (Region.br 0 (.inl p.inner.initializer)).HasType [] (List.ofFn S ++ L) :=
    (NestedCfgMixedSyntax.shell_endpoints ok).1 ▸ he
  have unique := (Tm.synthRouteType?_sound ok.inner.initializerType).2.1
  have anchor : ∃ D : Ty Empty, S 0 = .coprod Payload D := by
    have index := localAt S L 0
    cases typed with
    | br hit arg =>
        cases arg with
        | inl init =>
            exact ⟨_, (unique _ init) ▸ Option.some.inj (index.symm.trans hit)⟩
  obtain ⟨D, head⟩ := anchor
  have row : ∃ (t : (p.outer.rows (outerKeep 0)).HasType [.coprod Payload D] (List.ofFn S ++ L))
      (a : J.obj (ctxObj M [.coprod Payload D]) ⟶ J.obj (labelObj M (List.ofFn S ++ L))), RegionDenotes J M t a := by
    rw [← head]
    exact ⟨_, b 0, rows 0⟩
  obtain ⟨_, _, row⟩ := row
  obtain ⟨_, selected⟩ := select_inner J M ok D row
  obtain ⟨T, actual⟩ := selected.cfg_readback J M
  have bound : (List.ofFn S ++ L).length = (List.ofFn Q ++ L).length + 1 := by simp
  have trimmed := CfgDenotesAt.restrict J M innerKeep T (L := List.ofFn S ++ L) roll
    (by rw [bound]; exact ok.inner.entryScope) (fun i => by rw [bound]; exact ok.inner.rowScope i) actual
  obtain ⟨ent, blocks, _⟩ := trimmed
  have eq := ok.inner.retained_types ent blocks
  rw [eq] at ent blocks
  have anchored := NestedCfgMixedSyntax.ordinary_types ok
    (NestedCfgMixedSyntax.nested_type ok ent blocks) (fun j => hr j.succ)
  exact ⟨D, funext (Fin.cases head anchored)⟩

private theorem compare_reduced (ok : p.Valid outerKeep innerKeep P Q r L)
    (roll : IterationRolling C) (D : Ty Empty) {f g : Arrow}
    (small : CfgDenotesAt J M (stateTypes Payload Q) (.br 0 p.inner.initializer) p.commonRows f)
    (wide : CfgDenotesAt J M (stateTypes (.coprod Payload D) Q) p.outer.entry LiveRows g) :
    f = g := by
  have arg := (Tm.synthRouteType?_sound ok.inner.initializerType).2.2
  have entry : RegionConstructorRoutes M (post M Payload D Q L) (𝟙 _) [] (.br 0 p.inner.initializer) p.outer.entry := by
    rw [(NestedCfgMixedSyntax.shell_endpoints ok).1]
    refine .inl (localAt (stateTypes Payload Q) L 0) (localAt (stateTypes (.coprod Payload D) Q) L 0) arg ?_
    rw [Category.comp_id]
    exact post_zero M Payload D Q L
  have mapped := CfgDenotesAt.postmap_of_slot_squares J M (slot M Payload D Q) (𝟙 (labelObj M L))
    (fun _ _ _ _ de dw => by
      have eq := RegionConstructorRoutes.denotes J M entry de dw
      rw [J.map_id, Category.comp_id] at eq
      exact append_cut M J eq.symm)
    (fun i => Fin.cases (fun _ _ a b ds dw => by
      obtain ⟨_, selected⟩ := select_inner J M ok D dw
      obtain ⟨_, smallInner⟩ := cast_denotes J M (labels_eq Payload Q L) ds
      obtain ⟨_, wideInner⟩ := cast_denotes J M (labels_eq (.coprod Payload D) Q L) selected
      have mapped := ok.inner.postmap_inner J M roll D smallInner wideInner
      have eq := uncast_postmap M J (labels_eq Payload Q L) (labels_eq (.coprod Payload D) Q L) mapped
      have component := append_cut M J (A := Payload) (D := D) (Q := Q) (L := L) (Γ := [Payload])
        (show (J.map (Env ◁ injectLeft M Payload D) ≫ b) =
          a ≫ J.map (post M Payload D Q L) from eq)
      rw [Category.assoc] at component
      exact component)
      (fun i => by
        intro _ _ _ _ ds dw
        have route := checked_routes M Payload D Q L (Region.checkRoutes?_sound (ok.ordinaryRoutes i))
        have eq := RegionConstructorRoutes.denotes J M route ds dw
        rw [J.map_id, Category.comp_id] at eq
        change J.map (Env ◁ 𝟙 (M.obj (Q i))) ≫ _ ≫ _ = _
        rw [MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]
        exact append_cut M J eq.symm) i)
    small wide
  rwa [J.map_id, Category.comp_id, eq_comm] at mapped

private theorem compare_checked (ok : p.Valid outerKeep innerKeep P Q r L) (roll : IterationRolling C)
    {h h' : r.HasType [] L} {f g : Arrow}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g := by
  have init := (Tm.synthRouteType?_sound ok.inner.initializerType).1
  have shape : (NestedAdmission.Finite.layout P (List.ofFn Q ++ L) Payload).map Prod.fst =
      List.ofFn P ++ Payload :: (List.ofFn Q ++ L) := by
    simp [NestedAdmission.Finite.layout, List.map_ofFn, Function.comp_def, List.map_map]
  have selected : p.inner.commonInner.HasType [Payload] (labels Payload Q L) := by
    rw [labels_eq]
    exact .cfg P (shape ▸ (Region.checkRoutes?_sound ok.inner.entryRoute).hasType)
      (fun i => shape ▸ (Region.checkRoutes?_sound (ok.inner.rowRoutes i)).hasType)
  have ordinary (i : Fin q) : (p.commonOrdinary i).HasType [Q i] (labels Payload Q L) := by
    have typed := (Region.checkRoutes?_sound (ok.ordinaryRoutes i)).hasType
    simpa [labels_eq, layout, List.map_map, Function.comp_def] using typed
  have rows : ∀ i, (p.commonRows i).HasType [stateTypes Payload Q i] (labels Payload Q L) :=
    Fin.cases selected ordinary
  obtain ⟨base, small⟩ := CfgDenotesAt.exists_of_typing J M (stateTypes Payload Q) (L := L)
    (.br (localAt (stateTypes Payload Q) L 0) init) rows
  have agree {ht : r.HasType [] L} {b : Arrow} (w : RegionDenotes J M ht b) : base = b := by
    obtain ⟨_, _, wide⟩ := ok.outer.readback J M roll w
    obtain ⟨D, eq⟩ := align J M ok roll wide
    rw [eq] at wide
    exact compare_reduced J M ok roll D small wide
  exact (agree left).symm.trans (agree right)

theorem compare (roll : IterationRolling C) (ok : compare? outerKeep innerKeep P Q r L = .certified)
    {h h' : r.HasType [] L} {f g : Arrow}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g := by
  cases check : check? outerKeep innerKeep P Q r L with
  | none => simp [compare?, check] at ok
  | some plan => exact compare_checked J M (NestedCfgMixedSyntax.valid check) roll left right

end Model

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMixedAdmission
