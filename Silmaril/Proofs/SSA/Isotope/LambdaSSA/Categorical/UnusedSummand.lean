module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Readback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.ReplaceNewest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Renaming.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Renaming.Product.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

/-! # Read the state factorization from typed row witnesses -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel bind_pre_map case_pre_map case_postcomp)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind caseWithContext contextualLoop)

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]

section Labels

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty κ) V) {n : Nat} (R : Fin n → Ty κ)

local notation "Small" => labelObj M (List.ofFn R)
local notation "Wide" D => family R (some D)
local notation "Big" D => labelObj M (List.ofFn (Wide D))

private noncomputable abbrev tag (D : Fin n → Ty κ) (i : Fin n) :
    M.obj (R i) ⟶ M.obj ((Wide D) i) :=
  coprod.inl ≫ (M.coprodIso (R i) (D i)).inv

local notation "embedding" => embedLabels

private noncomputable def mapSlotFinite {Q : Fin n → Ty κ}
    (slot : ∀ i, M.obj (R i) ⟶ M.obj (Q i)) : finiteLabelObj M R ⟶ finiteLabelObj M Q :=
  Sigma.desc fun i => slot i ≫ finiteLabelInject M Q i

@[reassoc] theorem mapSlot_inject {Q : Fin n → Ty κ}
    (slot : ∀ i, M.obj (R i) ⟶ M.obj (Q i)) (i : Fin n)
    (hi : At (List.ofFn R) i (R i)) (hj : At (List.ofFn Q) i (Q i)) :
    labelInject M i hi ≫ mapSlotLabels M slot = slot i ≫ labelInject M i hj := by
  unfold mapSlotLabels
  erw [← Category.assoc, labelObjToFinite_local M R i hi]
  exact Sigma.ι_comp_desc _ _

@[reassoc] private theorem mapSlot_finite_inject {Q : Fin n → Ty κ}
    (slot : ∀ i, M.obj (R i) ⟶ M.obj (Q i)) (i : Fin n) :
    finiteLabelInject M R i ≫ mapSlotFinite M R slot = slot i ≫ finiteLabelInject M Q i :=
  Sigma.ι_comp_desc _ _

private theorem mapSlot_toFinite {Q : Fin n → Ty κ} (slot : ∀ i, M.obj (R i) ⟶ M.obj (Q i)) :
    mapSlotLabels M slot ≫ labelObjToFinite M Q =
      labelObjToFinite M R ≫ mapSlotFinite M R slot := by
  unfold mapSlotLabels
  erw [Category.assoc]
  congr 1
  apply Sigma.hom_ext
  intro i
  change finiteLabelInject M R i ≫ _ = finiteLabelInject M R i ≫ _
  erw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, labelObjToFinite_local, mapSlot_finite_inject]

private noncomputable abbrev finiteEmbedding (D : Fin n → Ty κ) :=
  mapSlotFinite M R (tag M R D)

@[reassoc] private theorem label_embed (D : Fin n → Ty κ) (i : Fin n) :
    labelInject M i (local_label R i) ≫ embedding M R D =
      tag M R D i ≫ labelInject M i (local_label (Wide D) i) :=
  mapSlot_inject M R (tag M R D) i _ _

private theorem finite_embed (D : Fin n → Ty κ) (i : Fin n) :
    finiteLabelInject M R i ≫ finiteEmbedding M R D = tag M R D i ≫ finiteLabelInject M (Wide D) i :=
  mapSlot_finite_inject M R (tag M R D) i

private theorem embedding_toFinite (D : Fin n → Ty κ) :
    embedding M R D ≫ labelObjToFinite M (Wide D) =
      labelObjToFinite M R ≫ finiteEmbedding M R D :=
  mapSlot_toFinite M R (tag M R D)

private theorem consMap_at {A B : Ty κ} (L : LCtx (Ty κ)) (h : M.obj A ⟶ M.obj B)
    (i : Fin (A :: L).length) :
    labelInject M i (labelAt_get (A :: L) i) ≫ mapLabelHead M L h = mapLabelHeadComponent M L h i := by
  have inj : labelInject M i (labelAt_get (A :: L) i) =
      Sigma.ι (fun j : Fin (A :: L).length => M.obj ((A :: L).get j)) i := by
    unfold labelInject
    change eqToHom (rfl : M.obj ((A :: L).get i) = M.obj ((A :: L).get i)) ≫
      Sigma.ι (fun j : Fin (A :: L).length => M.obj ((A :: L).get j)) i = _
    rw [eqToHom_refl, Category.id_comp]
  rw [inj]
  exact Sigma.ι_comp_desc _ _

@[reassoc] theorem mapHead_zero {A B : Ty κ} (L : LCtx (Ty κ)) (h : M.obj A ⟶ M.obj B) :
    labelInject M 0 (rfl : At (A :: L) 0 A) ≫ mapLabelHead M L h =
      h ≫ labelInject M 0 (rfl : At (B :: L) 0 B) :=
  consMap_at M L h 0

@[reassoc] theorem mapHead_succ {A B T : Ty κ} (L : LCtx (Ty κ)) (h : M.obj A ⟶ M.obj B)
    {i : Nat} (hi : At L i T) :
    labelInject M (i + 1) (show At (A :: L) (i + 1) T from hi) ≫ mapLabelHead M L h =
      labelInject M (i + 1) (show At (B :: L) (i + 1) T from hi) := by
  have atIndex (j : Fin L.length) (T : Ty κ) (hit : At L j T) :
      labelInject M (j.val + 1) (show At (A :: L) (j.val + 1) T from hit) ≫ mapLabelHead M L h =
        labelInject M (j.val + 1) (show At (B :: L) (j.val + 1) T from hit) := by
    have eq : L.get j = T := Option.some.inj ((labelAt_get L j).symm.trans hit)
    subst T
    exact consMap_at M L h j.succ
  exact atIndex ⟨i, (List.getElem?_eq_some_iff.mp hi).1⟩ T hi

private noncomputable def labelChange (tails : Option (Fin n → Ty κ)) :
    Small ⟶ labelObj M (List.ofFn (family R tails)) :=
  match tails with
  | none => 𝟙 _
  | some D => embedding M R D

noncomputable def payloadChange (tails : Option (Fin n → Ty κ)) (i : Fin n) :
    M.obj (R i) ⟶ M.obj (family R tails i) :=
  match tails with
  | none => 𝟙 _
  | some D => tag M R D i

theorem payloadChange_none (i : Fin n) : payloadChange M R none i = 𝟙 (M.obj (R i)) := by
  rw [payloadChange]

theorem payloadChange_some (D : Fin n → Ty κ) (i : Fin n) :
    payloadChange M R (some D) i = coprod.inl ≫ (M.coprodIso (R i) (D i)).inv := by
  rw [payloadChange]
  rfl

private noncomputable def finiteChange (tails : Option (Fin n → Ty κ)) :
    finiteLabelObj M R ⟶ finiteLabelObj M (family R tails) :=
  match tails with
  | none => 𝟙 _
  | some D => finiteEmbedding M R D

private theorem finite_change_inject (tails : Option (Fin n → Ty κ)) (i : Fin n) :
    finiteLabelInject M R i ≫ finiteChange M R tails =
      payloadChange M R tails i ≫ finiteLabelInject M (family R tails) i := by
  cases tails with
  | none => simp only [family, finiteChange, payloadChange, Category.comp_id, Category.id_comp]
  | some D => exact finite_embed M R D i

private theorem change_toFinite (tails : Option (Fin n → Ty κ)) :
    labelChange M R tails ≫ labelObjToFinite M (family R tails) =
      labelObjToFinite M R ≫ finiteChange M R tails := by
  cases tails with
  | none => simp only [family, labelChange, finiteChange, Category.comp_id, Category.id_comp]
  | some D => exact embedding_toFinite M R D

end Labels

section Graph

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty κ) V) [InstructionModel J M Φ]

variable {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)}

local notation "Small" => labelObj M (List.ofFn R)
local notation "ExitObj" => labelObj M L

omit [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [InstructionModel J M Φ] in
theorem bind_transfer {D E A B Q X : V} [DistributiveFreydCategory J]
    (p : D ⟶ E) (value : J.obj E ⟶ J.obj A)
    {actual : J.obj (D ⊗ A) ⟶ J.obj Q} {body : J.obj (E ⊗ A) ⟶ J.obj B}
    {cut : J.obj Q ⟶ J.obj X} {route : J.obj B ⟶ J.obj X}
    (body_eq : actual ≫ cut = J.map (p ▷ A) ≫ body ≫ route) :
    bind J (J.map p ≫ value) actual ≫ cut = J.map p ≫ bind J value body ≫ route := by
  calc
    _ = bind J (J.map p ≫ value) (actual ≫ cut) := Category.assoc _ _ _
    _ = bind J (J.map p ≫ value) (J.map (p ▷ A) ≫ body) ≫ route := by
      simp only [body_eq, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc]
    _ = _ := by rw [bind_pre_map, Category.assoc]

private noncomputable def eval {Γ : VCtx (Ty κ)} :
    Row (Φ := Φ) R L Γ → (J.obj (ctxObj M Γ) ⟶ J.obj (ExitObj ⨿ Small))
  | .jump i arg => denote J M (operand_base arg) ≫
      J.map (labelInject M i (local_label R i) ≫ coprod.inr)
  | .let₁ value body => bind J (denote J M (operand_base value)) (eval body)
  | .let₂ value body => bindProduct J M (denote J M (operand_base value)) (eval body)
  | .exit i hit arg => denote J M (operand_base arg) ≫ J.map (labelInject M i hit ≫ coprod.inl)
  | .case arg left right => caseWithContext J
      (denote J M (operand_base arg) ≫ J.map (M.coprodIso _ _).hom)
      (eval left) (eval right)

set_option backward.isDefEq.respectTransparency false in
private theorem row_eval {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (reads : ∀ ⦃i A⦄ (h : At Γ i A), p ≫ lookup M i h = lookup M (ρ i) (ren h))
    (tails : Option (Fin n → Ty κ)) (r : Row (Φ := Φ) R L Γ) :
    ∃ f, RegionDenotes J M (row_typed ren tails r) f ∧
      f ≫ J.map (labelAppendSplit M (List.ofFn (family R tails)) L) =
        J.map p ≫ eval J M r ≫ J.map (coprod.map (𝟙 ExitObj) (labelChange M R tails)) := by
  induction r generalizing Δ ρ with
  | jump i a =>
      have da := (denote_spec J M (operand_base a)).rename J M ren reads
      cases tails with
      | none =>
          refine ⟨_, RegionDenotes.br (h := local_append R L i) da, ?_⟩
          simp only [eval, family, labelChange, coprod.map_id_id, J.map_id, Category.comp_id,
            Category.assoc, ← J.map_comp]
          erw [labelAppendSplit_local M R L i (local_append R L i) (local_label R i)]
      | some D =>
          refine ⟨_, RegionDenotes.br (h := local_append (family R (some D)) L i) (Denotes.inl (B := D i) da), ?_⟩
          simp only [eval, Category.assoc, ← J.map_comp, labelChange, coprod.inr_map]
          erw [labelAppendSplit_local M (family R (some D)) L i
            (local_append (family R (some D)) L i) (local_label (family R (some D)) i),
            label_embed_assoc M R D i]
          simp only [tag, Category.assoc]
  | exit i hit a =>
      have da := (denote_spec J M (operand_base a)).rename J M ren reads
      refine ⟨_, RegionDenotes.br (h := exit_append (family R tails) hit) da, ?_⟩
      simp only [eval, Category.assoc, ← J.map_comp, coprod.inl_map, Category.id_comp]
      erw [labelAppendSplit_exit M (family R tails) L hit (exit_append (family R tails) hit)]
  | @let₁ Γ A value body ih =>
      have dv := (denote_spec J M (operand_base value)).rename J M ren reads
      obtain ⟨_, db, body_eq⟩ := ih (ren.lift A) (p ▷ M.obj A) (lookup_liftRename M ren reads A)
      refine ⟨_, RegionDenotes.let₁ dv db, ?_⟩
      simpa only [eval] using bind_transfer J p (denote J M (operand_base value)) body_eq
  | @let₂ Γ A B value body ih =>
      have dv := (denote_spec J M (operand_base value)).rename J M ren reads
      obtain ⟨_, db, body_eq⟩ := ih ((ren.lift A).lift B) ((p ▷ M.obj A) ▷ M.obj B)
        (lookup_liftRename M (ren.lift A) (lookup_liftRename M ren reads A) B)
      refine ⟨_, RegionDenotes.let₂ dv db, ?_⟩
      simpa only [eval, bindProduct, ctxObj] using bindProduct_transfer J M p (denote J M (operand_base value)) body_eq
  | @case Γ A B a l r ihl ihr =>
      have da := (denote_spec J M (operand_base a)).rename J M ren reads
      obtain ⟨fl, dl, left⟩ := ihl (ren.lift A) (p ▷ M.obj A) (lookup_liftRename M ren reads A)
      obtain ⟨fr, dr, right⟩ := ihr (ren.lift B) (p ▷ M.obj B) (lookup_liftRename M ren reads B)
      refine ⟨_, RegionDenotes.case da dl dr, ?_⟩
      simp only [eval, case_postcomp, left, right, Category.assoc]
      rw [case_pre_map]

private theorem cut_eq {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (reads : ∀ ⦃i A⦄ (h : At Γ i A), p ≫ lookup M i h = lookup M (ρ i) (ren h))
    (tails : Option (Fin n → Ty κ)) (r : Row (Φ := Φ) R L Γ)
    {f : J.obj (ctxObj M Δ) ⟶ J.obj (labelObj M (List.ofFn (family R tails) ++ L))}
    (w : RegionDenotes J M (row_typed ren tails r) f) :
    f ≫ J.map (labelAppendSplit M (List.ofFn (family R tails)) L) =
      J.map p ≫ eval J M r ≫ J.map (coprod.map (𝟙 ExitObj) (labelChange M R tails)) := by
  obtain ⟨_, d, computed⟩ := row_eval J M ren p reads tails r
  rw [(row_determined ren tails r).denotes_eq J M w d, computed]

theorem row_comparison {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (ren : Ren Γ Δ ρ)
    (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (reads : ∀ ⦃i A⦄ (h : At Γ i A), p ≫ lookup M i h = lookup M (ρ i) (ren h))
    (D : Fin n → Ty κ) (r : Row (Φ := Φ) R L Γ)
    {ts : (r.region false id).HasType Γ (List.ofFn R ++ L)}
    {tl : (r.region true ρ).HasType Δ (List.ofFn (family R (some D)) ++ L)}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    {g : J.obj (ctxObj M Δ) ⟶ J.obj (labelObj M (List.ofFn (family R (some D)) ++ L))}
    (small : RegionDenotes J M ts f) (wide : RegionDenotes J M tl g) :
    g ≫ J.map (labelAppendSplit M (List.ofFn (family R (some D))) L) =
      J.map p ≫ f ≫ J.map (labelAppendSplit M (List.ofFn R) L) ≫
        J.map (coprod.map (𝟙 ExitObj) (embedLabels M R D)) := by
  have before := cut_eq J M (Ren.id Γ) (𝟙 (ctxObj M Γ)) (fun _ _ _ => Category.id_comp _)
    none r small
  have after := cut_eq J M ren p reads (some D) r wide
  simp only [family, labelChange] at before
  erw [coprod.map_id_id, J.map_id, J.map_id, Category.id_comp, Category.comp_id] at before
  rw [← Category.assoc f, before]
  exact after

section Program

variable {k : Nat} {P : Fin (k + 1) → Ty κ} {K : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

local notation "Env" => ctxObj M Γ
local notation "Result" => labelObj M K
local notation "Local" => labelObj M (List.ofFn P)

set_option backward.isDefEq.respectTransparency false in
private theorem taken_tag_row (D : Fin (k + 1) → Ty κ) (i : Fin (k + 1))
    (row : Row (Φ := Φ) P K (P i :: Γ)) {raw : Region Φ}
    (prune : Region.PruneConstructorTests (raw.substVars (Tm.replaceNewest (.inl (.var 0))))
      (row.region true id))
    {ts : (row.region false id).HasType (P i :: Γ) (List.ofFn P ++ K)}
    {tw : raw.HasType (family P (some D) i :: Γ) (List.ofFn (family P (some D)) ++ K)}
    {f : J.obj (ctxObj M (P i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn P ++ K))}
    {g : J.obj (ctxObj M (family P (some D) i :: Γ)) ⟶
      J.obj (labelObj M (List.ofFn (family P (some D)) ++ K))}
    (small : RegionDenotes J M ts f) (wide : RegionDenotes J M tw g) :
    J.map (Env ◁ tag M P D i) ≫ g ≫ J.map (labelAppendSplit M (List.ofFn (family P (some D))) K) =
      f ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
        J.map (coprod.map (𝟙 Result) (embedLabels M P D)) := by
  have da : Denotes J M (.inl (.var rfl) (B := D i) :
      (Tm.inl (.var 0) : Tm Φ).HasType (P i :: Γ) (Silmaril.coprod (P i) (D i)))
      (J.map (snd Env (M.obj (P i)) ≫ tag M P D i)) := by
    rw [J.map_comp]
    simpa only [tag, lookup] using
      (Denotes.inl (J := J) (M := M) (B := D i)
        (Denotes.var (J := J) (M := M) (show At (P i :: Γ) 0 (P i) from rfl)))
  obtain ⟨_, restricted⟩ := wide.replaceNewest J M da
  obtain ⟨_, selected⟩ := prune.denotes J M restricted
  have compared := row_comparison J M (Ren.id _) (𝟙 _) (fun _ _ _ => Category.id_comp _)
    D row small selected
  rw [J.map_id, Category.id_comp, Category.assoc] at compared
  exact compared

theorem slot_postmap {Q : Fin (k + 1) → Ty κ}
    (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) {K' : LCtx (Ty κ)}
    (out : Result ⟶ labelObj M K')
    {entry entry' : Region Φ} {rows rows' : Fin (k + 1) → Region Φ}
    (entryRoute : ∀ ⦃ts : entry.HasType Γ (List.ofFn P ++ K)⦄
      ⦃tw : entry'.HasType Γ (List.ofFn Q ++ K')⦄
      ⦃a : J.obj Env ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj Env ⟶ J.obj (labelObj M (List.ofFn Q ++ K'))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      b ≫ J.map (labelAppendSplit M (List.ofFn Q) K') =
        a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
          J.map (coprod.map out (mapSlotLabels M slot)))
    (rowRoutes : ∀ i
      ⦃ts : (rows i).HasType (P i :: Γ) (List.ofFn P ++ K)⦄
      ⦃tw : (rows' i).HasType (Q i :: Γ) (List.ofFn Q ++ K')⦄
      ⦃a : J.obj (ctxObj M (P i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj (ctxObj M (Q i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn Q ++ K'))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      J.map (Env ◁ (slot i)) ≫
        b ≫ J.map (labelAppendSplit M (List.ofFn Q) K') =
          a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
            J.map (coprod.map out (mapSlotLabels M slot)))
    {f : J.obj Env ⟶ J.obj Result}
    {g : J.obj Env ⟶ J.obj (labelObj M K')}
    (small : CfgDenotesAt J M P entry rows f)
    (wide : CfgDenotesAt J M Q entry' rows' g) : g = f ≫ J.map out := by
  let h := mapSlotLabels M slot
  let hf := mapSlotFinite M P slot
  let cut := labelAppendSplit M (List.ofFn P) K
  let cut' := labelAppendSplit M (List.ofFn Q) K'
  obtain ⟨_, _, e, b, all, se, sb, sc, rfl⟩ := small
  obtain ⟨_, _, e', b', all', we, wb, wc, rfl⟩ := wide
  have entry_eq : e' ≫ J.map cut' = e ≫ J.map cut ≫ J.map (coprod.map out h) := entryRoute se we
  have row_eq : J.map (Env ◁ hf) ≫ all' ≫ J.map cut' =
      all ≫ J.map cut ≫ J.map (coprod.map out h) := by
    apply collective_ext J M k Γ P
    intro i
    rw [MonoidalCategory.id_tensorHom]
    have sh := sc.restrict i
    have wh := wc.restrict i
    rw [MonoidalCategory.id_tensorHom] at sh wh
    have slide : J.map (Env ◁ finiteLabelInject M P i) ≫ J.map (Env ◁ hf) =
        J.map (Env ◁ (slot i)) ≫ J.map (Env ◁ finiteLabelInject M Q i) := by
      rw [← J.map_comp, ← J.map_comp, ← MonoidalCategory.whiskerLeft_comp,
        ← MonoidalCategory.whiskerLeft_comp, mapSlot_finite_inject]
    rw [← Category.assoc, slide, Category.assoc, ← Category.assoc _ all', wh,
      ← Category.assoc _ all, sh]
    exact rowRoutes i (sb i) (wb i)
  have square :
      (J.map (Env ◁ labelObjToFinite M P) ≫ all ≫ J.map cut) ≫
          J.map (coprod.map out h) =
        J.map (Env ◁ h) ≫ J.map (Env ◁ labelObjToFinite M Q) ≫ all' ≫ J.map cut' := by
    rw [← Category.assoc (J.map (Env ◁ h)), ← J.map_comp,
      ← MonoidalCategory.whiskerLeft_comp, mapSlot_toFinite, MonoidalCategory.whiskerLeft_comp,
      J.map_comp]
    simp only [Category.assoc]
    rw [← row_eq]
  unfold cfgDispatchArrow
  rw [MonoidalCategory.id_tensorHom, MonoidalCategory.id_tensorHom, entry_eq]
  simpa only [Category.assoc] using cfgDispatch_of_exit_state_square J out h (e ≫ J.map cut) _ _ square

theorem taken_tag_postmap (D : Fin (k + 1) → Ty κ) {K' : LCtx (Ty κ)}
    (out : Result ⟶ labelObj M K')
    {entry entry' : Region Φ} {rows rows' : Fin (k + 1) → Region Φ}
    (entryRoute : ∀ ⦃ts : entry.HasType Γ (List.ofFn P ++ K)⦄
      ⦃tw : entry'.HasType Γ (List.ofFn (family P (some D)) ++ K')⦄
      ⦃a : J.obj Env ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj Env ⟶ J.obj (labelObj M (List.ofFn (family P (some D)) ++ K'))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      b ≫ J.map (labelAppendSplit M (List.ofFn (family P (some D))) K') =
        a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
          J.map (coprod.map out (embedLabels M P D)))
    (rowRoutes : ∀ i
      ⦃ts : (rows i).HasType (P i :: Γ) (List.ofFn P ++ K)⦄
      ⦃tw : (rows' i).HasType (family P (some D) i :: Γ) (List.ofFn (family P (some D)) ++ K')⦄
      ⦃a : J.obj (ctxObj M (P i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj (ctxObj M (family P (some D) i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn (family P (some D)) ++ K'))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      J.map (Env ◁ (coprod.inl ≫ (M.coprodIso (P i) (D i)).inv)) ≫
        b ≫ J.map (labelAppendSplit M (List.ofFn (family P (some D))) K') =
          a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
            J.map (coprod.map out (embedLabels M P D)))
    {f : J.obj Env ⟶ J.obj Result}
    {g : J.obj Env ⟶ J.obj (labelObj M K')}
    (small : CfgDenotesAt J M P entry rows f)
    (wide : CfgDenotesAt J M (family P (some D)) entry' rows' g) : g = f ≫ J.map out :=
  slot_postmap J M (tag M P D) out entryRoute rowRoutes small wide

theorem taken_tag_of_squares (D : Fin (k + 1) → Ty κ)
    {entry entry' : Region Φ} {rows rows' : Fin (k + 1) → Region Φ}
    (entryRoute : ∀ ⦃ts : entry.HasType Γ (List.ofFn P ++ K)⦄
      ⦃tw : entry'.HasType Γ (List.ofFn (family P (some D)) ++ K)⦄
      ⦃a : J.obj Env ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj Env ⟶ J.obj (labelObj M (List.ofFn (family P (some D)) ++ K))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      b ≫ J.map (labelAppendSplit M (List.ofFn (family P (some D))) K) =
        a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
          J.map (coprod.map (𝟙 Result) (embedLabels M P D)))
    (rowRoutes : ∀ i
      ⦃ts : (rows i).HasType (P i :: Γ) (List.ofFn P ++ K)⦄
      ⦃tw : (rows' i).HasType (family P (some D) i :: Γ) (List.ofFn (family P (some D)) ++ K)⦄
      ⦃a : J.obj (ctxObj M (P i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj (ctxObj M (family P (some D) i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn (family P (some D)) ++ K))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      J.map (Env ◁ (coprod.inl ≫ (M.coprodIso (P i) (D i)).inv)) ≫
        b ≫ J.map (labelAppendSplit M (List.ofFn (family P (some D))) K) =
          a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
            J.map (coprod.map (𝟙 Result) (embedLabels M P D)))
    {f g : J.obj Env ⟶ J.obj Result}
    (small : CfgDenotesAt J M P entry rows f)
    (wide : CfgDenotesAt J M (family P (some D)) entry' rows' g) : f = g := by
  have mapped := taken_tag_postmap J M D (𝟙 Result) entryRoute rowRoutes small wide
  rw [J.map_id, Category.comp_id] at mapped
  exact mapped.symm

theorem taken_tag_agreement (D : Fin (k + 1) → Ty κ) (entry : Row (Φ := Φ) P K Γ)
    (rows : ∀ i, Row (Φ := Φ) P K (P i :: Γ)) (raw : Fin (k + 1) → Region Φ)
    (prune : ∀ i, Region.PruneConstructorTests
      ((raw i).substVars (Tm.replaceNewest (.inl (.var 0)))) ((rows i).region true id))
    {f g : J.obj Env ⟶ J.obj Result}
    (small : CfgDenotesAt J M P (entry.region false id) (fun i => (rows i).region false id) f)
    (wide : CfgDenotesAt J M (family P (some D)) (entry.region true id) raw g) : f = g := by
  refine taken_tag_of_squares J M D ?_ ?_ small wide
  · intro _ _ _ _ se we
    simpa only [J.map_id, Category.id_comp] using
      row_comparison J M (Ren.id _) (𝟙 _) (fun _ _ _ => Category.id_comp _) D entry se we
  · intro i _ _ _ _ sb wb
    exact taken_tag_row J M D i (rows i) (prune i) sb wb

private theorem dispatch_of_rows (roll : IterationRolling C)
    (p : Program (Φ := Φ) P K Γ) (tails : Option (Fin (k + 1) → Ty κ))
    (small : J.obj (Env ⊗ finiteLabelObj M P) ⟶ J.obj (Result ⨿ Local))
    (small_rows : ∀ i, J.map ((𝟙 Env) ⊗ₘ finiteLabelInject M P i) ≫ small =
      J.map (fst Env (M.obj (P i))) ≫ eval J M (p.blocks i))
    {e : J.obj Env ⟶ J.obj (labelObj M (List.ofFn (family P tails) ++ K))}
    {bs : ∀ i, J.obj (ctxObj M (family P tails i :: Γ)) ⟶
      J.obj (labelObj M (List.ofFn (family P tails) ++ K))}
    {large : J.obj (Env ⊗ finiteLabelObj M (family P tails)) ⟶
      J.obj (labelObj M (List.ofFn (family P tails) ++ K))}
    (entry : RegionDenotes J M (row_typed (Ren.id Γ) tails p.entry) e)
    (blocks : ∀ i, RegionDenotes J M
      (row_typed (Ren.wk Γ (family P tails i)) tails (p.blocks i)) (bs i))
    (rows : CollectiveDenotes J M Γ (family P tails) K bs large) :
    caseWithContext J
      (e ≫ J.map (labelAppendSplit M (List.ofFn (family P tails)) K)) (J.map (snd Env Result))
      (contextualLoop J
        (J.map ((𝟙 Env) ⊗ₘ labelObjToFinite M (family P tails)) ≫ large ≫
          J.map (labelAppendSplit M (List.ofFn (family P tails)) K))) =
    caseWithContext J (eval J M p.entry) (J.map (snd Env Result))
      (contextualLoop J (J.map (Env ◁ labelObjToFinite M P) ≫ small)) := by
  let S := family P tails
  let h := labelChange M P tails
  let hf := finiteChange M P tails
  let cut := labelAppendSplit M (List.ofFn S) K
  let inject (i : Fin (k + 1)) := payloadChange M P tails i
  obtain ⟨mid, mid_rows⟩ := collective_exists J M k Γ S (Result ⨿ Local)
    (fun i => J.map (fst Env (M.obj (S i))) ≫ eval J M (p.blocks i))
  have entry_eq : e ≫ J.map cut =
      eval J M p.entry ≫ J.map (coprod.map (𝟙 Result) h) := by
    have computed := cut_eq J M (Ren.id Γ) (𝟙 Env) (fun _ _ _ => Category.id_comp _)
      tails p.entry entry
    rw [J.map_id, Category.id_comp] at computed
    exact computed
  have before : J.map (Env ◁ hf) ≫ mid = small := by
    apply collective_ext J M k Γ P
    intro i
    rw [MonoidalCategory.id_tensorHom]
    have selected := small_rows i
    rw [MonoidalCategory.id_tensorHom] at selected
    rw [selected]
    have slide :
        J.map (Env ◁ finiteLabelInject M P i) ≫ J.map (Env ◁ hf) ≫ mid =
          J.map (Env ◁ inject i) ≫ J.map ((𝟙 Env) ⊗ₘ finiteLabelInject M S i) ≫ mid := by
      rw [MonoidalCategory.id_tensorHom, ← J.map_comp_assoc, ← J.map_comp_assoc,
        ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
      exact congrArg (fun f => J.map (Env ◁ f) ≫ mid) (finite_change_inject M P tails i)
    erw [slide, mid_rows i, ← J.map_comp_assoc, CartesianMonoidalCategory.whiskerLeft_fst]
  have after : large ≫ J.map cut = mid ≫ J.map (coprod.map (𝟙 Result) h) := by
    apply collective_ext J M k Γ S
    intro i
    erw [← Category.assoc _ large, rows.restrict i, ← Category.assoc _ mid, mid_rows i, Category.assoc]
    exact cut_eq J M (Ren.wk Γ (S i)) (fst Env (M.obj (S i))) (fun _ _ _ => rfl) tails
      (p.blocks i) (blocks i)
  let middle := J.map (Env ◁ labelObjToFinite M S) ≫ mid
  have commute : J.map (Env ◁ h) ≫ middle = J.map (Env ◁ labelObjToFinite M P) ≫ small := by
    unfold middle
    rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp]
    erw [change_toFinite M P tails]
    rw [MonoidalCategory.whiskerLeft_comp, J.map_comp, Category.assoc, before]
  have computed := cfgDispatch_of_state_factorization J roll h (eval J M p.entry) middle
  rw [commute] at computed
  unfold middle at computed
  rw [Category.assoc] at computed
  rw [MonoidalCategory.id_tensorHom, entry_eq, ← Category.assoc _ large, Category.assoc, after]
  exact computed.symm

theorem program_at_agreement (roll : IterationRolling C) (p : Program (Φ := Φ) P K Γ) :
    ∃ f : J.obj Env ⟶ J.obj Result, ∀ tails : Option (Fin (k + 1) → Ty κ),
      p.denotesAt J M tails f ∧ ∀ g, p.denotesAt J M tails g → g = f := by
  obtain ⟨small, small_rows⟩ := collective_exists J M k Γ P (Result ⨿ Local)
    (fun i => J.map (fst Env (M.obj (P i))) ≫ eval J M (p.blocks i))
  let common := caseWithContext J (eval J M p.entry) (J.map (snd Env Result))
    (contextualLoop J (J.map (Env ◁ labelObjToFinite M P) ≫ small))
  have compare (tails : Option (Fin (k + 1) → Ty κ)) (g : J.obj Env ⟶ J.obj Result)
      (w : p.denotesAt J M tails g) : g = common := by
    obtain ⟨_, _, _, _, _, entry, blocks, rows, rfl⟩ := w
    exact dispatch_of_rows J M roll p tails small small_rows entry blocks rows
  refine ⟨common, fun tails => ⟨?_, compare tails⟩⟩
  let S := family P tails
  let e := row_typed (Ren.id Γ) tails p.entry
  let steps (i : Fin (k + 1)) := row_typed (Ren.wk Γ (S i)) tails (p.blocks i)
  obtain ⟨g, w⟩ := CfgDenotesAt.exists_of_typing J M S e steps
  exact compare tails g w ▸ w

theorem program_agreement (roll : IterationRolling C) (p : Program (Φ := Φ) P K Γ) :
    ∃ f, ∀ (tails : Option (Fin (k + 1) → Ty κ)) (t : (p.region tails.isSome).HasType Γ K),
      RegionDenotes J M t f := by
  obtain ⟨f, agree⟩ := program_at_agreement J M roll p
  exact ⟨f, fun tails _ => (agree tails).1.denotes J M⟩

theorem program_witness_readback (p : Program (Φ := Φ) P K Γ) (covers : p.targetsEveryLabel)
    {tag : Bool} {t : (p.region tag).HasType Γ K} {f : J.obj Env ⟶ J.obj Result}
    (d : RegionDenotes J M t f) :
    ∃ tails : Option (Fin (k + 1) → Ty κ), tails.isSome = tag ∧ p.denotesAt J M tails f := by
  obtain ⟨S, selected⟩ := d.cfg_readback J M
  have compatible : ∃ tails : Option (Fin (k + 1) → Ty κ),
      tails.isSome = tag ∧ S = family P tails := by
    obtain ⟨he, hb, _, _, _, _, _, _, _⟩ := selected
    exact Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily.family_from_typing
      p covers tag he hb
  obtain ⟨tails, tag_eq, family_eq⟩ := compatible
  refine ⟨tails, tag_eq, ?_⟩
  unfold Program.denotesAt
  rw [tag_eq, ← family_eq]
  exact selected

theorem program_witness_eq (roll : IterationRolling C) (p : Program (Φ := Φ) P K Γ)
    (covers : p.targetsEveryLabel) {tag tag' : Bool}
    {t : (p.region tag).HasType Γ K} {t' : (p.region tag').HasType Γ K}
    {f g : J.obj Env ⟶ J.obj Result} (d : RegionDenotes J M t f) (e : RegionDenotes J M t' g) :
    f = g := by
  obtain ⟨_, agree⟩ := program_at_agreement J M roll p
  obtain ⟨left, _, d'⟩ := program_witness_readback J M p covers d
  obtain ⟨right, _, e'⟩ := program_witness_readback J M p covers e
  exact ((agree left).2 f d').trans ((agree right).2 g e').symm

end Program

end Graph

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof
