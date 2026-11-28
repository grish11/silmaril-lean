module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Proofs

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n}

local notation "Ops" => Opcode F
local notation "U" => Code.unit

open CategoryTheory CategoryTheory.Limits
open Region.Paper.Extension.Singleton
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (caseValueBranches)
open Silmaril.DeBruijn (lift)

set_option backward.isDefEq.respectTransparency false

variable {I J O P : Code}

private theorem value_rename (c : Code) (x : c.Value) (ρ : Nat → Nat) :
    (value c x : Tm Ops).rename ρ = value c x := by
  induction c with
  | unit => rfl
  | sum l r il ir => cases x <;> simp [value, Tm.rename, il, ir]

private theorem value_subst (c : Code) (x : c.Value) (σ : Nat → Tm Ops) :
    (value c x : Tm Ops).subst σ = value c x := by
  induction c with
  | unit => rfl
  | sum l r il ir => cases x <;> simp [value, Tm.subst, il, ir]

theorem Step.rename (s : Step F I O) (ρ : Nat → Nat) (h : ρ 0 = 0) :
    s.ssa.renameVars ρ = s.ssa := by
  induction s generalizing ρ with
  | lit x => simp [Step.ssa, Region.renameVars, value_rename]
  | call f x k ih =>
    simp [Step.ssa, Region.renameVars, Tm.rename, value_rename, ih (lift ρ) rfl]
  | split l r il ir =>
    simp [Step.ssa, Region.renameVars, Tm.rename, h, il (lift ρ) rfl, ir (lift ρ) rfl]

theorem Step.subst (s : Step F I O) (σ : Nat → Tm Ops) (h : σ 0 = .var 0) :
    s.ssa.substVars σ = s.ssa := by
  induction s generalizing σ with
  | lit x => simp [Step.ssa, Region.substVars, value_subst]
  | call f x k ih =>
    simp [Step.ssa, Region.substVars, Tm.subst, value_subst, ih (Tm.liftSubst σ) rfl]
  | split l r il ir =>
    simp [Step.ssa, Region.substVars, Tm.subst, h,
      il (Tm.liftSubst σ) rfl, ir (Tm.liftSubst σ) rfl]

theorem tabulate_source (c : Code) (rows : c.Value → Step F .unit O) :
    (tabulate c rows).source = c.dispatch (fun v => (rows v).source) (.var 0) := by
  induction c with
  | unit => rfl
  | sum l r il ir => simp [tabulate, Code.dispatch, Step.source, il, ir]

theorem row_source (r : Row F J O) (c : Code) :
    (row r c).source = r.source := by
  cases r with
  | ret b => rfl
  | call f x k => simp [row, Step.source, literals, tabulate_source, Row.source, replySource]

theorem tabulate_map (c : Code) (rows : c.Value → Step F .unit O) (f : O.Value → P.Value) :
    Step.mapOut f (tabulate c rows) = tabulate c (fun v => Step.mapOut f (rows v)) := by
  induction c with
  | unit => rfl
  | sum l r il ir => simp [tabulate, Step.mapOut, il, ir]

theorem row_map {J K : Code} (r : Row F J O) (c : Code) (f : J.Value → K.Value) :
    Step.mapOut (O := .sum O J) (P := .sum O K) (Sum.map id f) (row r c) = row (r.map f) c := by
  cases r with
  | ret b => rfl
  | call op x k => simp [row, Row.map, Step.mapOut, literals, tabulate_map]

variable {ε : Type} [HasEff (Opcode F) ε]

set_option hygiene false in
local notation "Seed[" p "]" => targetSeed (F := F) (ε := ε) p

section Category

variable (pe : ε)

set_option hygiene false in
local notation "Obj" => ofType (Seed[pe])

theorem exact_comp {A B C : Ty Unit} {r s : Region Ops}
    (hr : Region.ValueBranches [A] r [B]) (hs : Region.ValueBranches [B] s [C])
    (hrs : Region.ValueBranches [A] (Region.compLSubst (fun _ => r) (fun _ => s) 0) [C]) :
    ofRegion (Seed[pe]) hr ≫ ofRegion (Seed[pe]) hs = ofRegion (Seed[pe]) hrs := by
  change (projection (Seed[pe])).map _ ≫ (projection (Seed[pe])).map _ = _
  rw [← Functor.map_comp, Region.Paper.TypeCategory.ofRegion_comp hr hs hrs]

private theorem exact_region_congr {A B : Ty Unit} {r s : Region Ops} (eq : r = s)
    (hr : Region.ValueBranches [A] r [B]) (hs : Region.ValueBranches [A] s [B]) :
    ofRegion (Seed[pe]) hr = ofRegion (Seed[pe]) hs := by subst s; rfl

private theorem split_typed (l : Step F I O) (r : Step F J O) :
    Region.ValueBranches [(.sum I J : Code).ty]
      (.case (.var 0) (l.ssa.renameVars (lift Nat.succ)) (r.ssa.renameVars (lift Nat.succ))) [O.ty] :=
  caseValueBranches (l.typed []) (r.typed [])

theorem split_arrow (l : Step F I O) (r : Step F J O) :
    ((sumIso (Seed[pe]) I.ty J.ty).inv ≫ (Step.split l r).arrow pe) =
      coprod.desc (l.arrow pe) (r.arrow pe) := by
  have lhs := split_typed l r
  have hl : l.ssa.renameVars (lift Nat.succ) = l.ssa := Step.rename l _ rfl
  have hr : r.ssa.renameVars (lift Nat.succ) = r.ssa := Step.rename r _ rfl
  have same : ofRegion (Seed[pe]) lhs = (Step.split l r).arrow pe :=
    exact_region_congr pe (by simp only [Step.ssa, hl, hr]) lhs ((Step.split l r).typed [])
  rw [← same]
  apply coprod.hom_ext
  · conv_lhs => rw [← sumCofan_inl_sumIso_hom (Seed[pe]) I.ty J.ty,
      Category.assoc, Iso.hom_inv_id_assoc]
    rw [coprod.inl_desc]
    change (projection (Seed[pe])).map _ ≫ (projection (Seed[pe])).map _ = _
    rw [← Functor.map_comp, Region.Paper.RetainedCase.case_ofRegion_inl (l.typed []) (r.typed [])]
    rfl
  · conv_lhs => rw [← sumCofan_inr_sumIso_hom (Seed[pe]) I.ty J.ty,
      Category.assoc, Iso.hom_inv_id_assoc]
    rw [coprod.inr_desc]
    change (projection (Seed[pe])).map _ ≫ (projection (Seed[pe])).map _ = _
    rw [← Functor.map_comp, Region.Paper.RetainedCase.case_ofRegion_inr (l.typed []) (r.typed [])]
    rfl

private theorem request_typed (f : Ops) (x : f.argCode.Value) :
    Region.ValueBranches [I.ty] (.let₁ (.op f (value f.argCode x)) (.br 0 (.var 0))) [f.replyCode.ty] :=
  .let₁ (.op (value_typed _ x _).hasType) (.br rfl (.var rfl))

noncomputable def request (f : Ops) (x : f.argCode.Value) : Obj I.ty ⟶ Obj f.replyCode.ty :=
  ofRegion (Seed[pe]) (request_typed (I := I) f x)

theorem call_arrow (f : Ops) (x : f.argCode.Value) (s : Step F f.replyCode O) :
    (Step.call (I := I) f x s).arrow pe = request (I := I) pe f x ≫ s.arrow pe := by
  have eq : Region.compLSubst (fun _ => .let₁ (.op f (value f.argCode x)) (.br 0 (.var 0)))
      (fun _ => s.ssa) 0 = (Step.call (I := I) f x s).ssa := by
    simp only [Region.compLSubst, Region.lsubst, Region.liftLSubstVars,
      Step.rename s (lift Nat.succ) rfl, Step.subst s (Tm.singleSubst (.var 0)) rfl, Step.ssa]
  obtain ⟨h⟩ : Nonempty (Region.ValueBranches [I.ty]
      (Region.compLSubst (fun _ => .let₁ (.op f (value f.argCode x)) (.br 0 (.var 0))) (fun _ => s.ssa) 0)
      [O.ty]) := ⟨eq.symm ▸ (Step.call (I := I) f x s).typed []⟩
  exact (exact_region_congr pe eq h ((Step.call (I := I) f x s).typed [])).symm.trans
    (exact_comp pe (request_typed f x) (s.typed []) h).symm

private theorem leftTag (A B : Code) :
    Region.ValueBranches [A.ty] (.br 0 (.inl (.var 0)) : Region Ops) [(.sum A B : Code).ty] :=
  .br rfl (.inl (.var rfl))

private theorem rightTag (A B : Code) :
    Region.ValueBranches [B.ty] (.br 0 (.inr (.var 0)) : Region Ops) [(.sum A B : Code).ty] :=
  .br rfl (.inr (.var rfl))

noncomputable def left (A B : Code) : Obj A.ty ⟶ Obj (.sum A B : Code).ty :=
  ofRegion (Seed[pe]) (leftTag A B)

noncomputable def right (A B : Code) : Obj B.ty ⟶ Obj (.sum A B : Code).ty :=
  ofRegion (Seed[pe]) (rightTag A B)

private theorem left_coord (A B : Code) :
    left pe A B ≫ (sumIso (Seed[pe]) A.ty B.ty).hom = coprod.inl := by
  have h := congrArg ((projection (Seed[pe])).map) (Region.Paper.TypeCategory.sumCofan_inl (Φ := Ops) A.ty B.ty)
  change (sumCofan (Seed[pe]) A.ty B.ty).inl = left pe A B at h
  rw [← h, sumCofan_inl_sumIso_hom]

theorem right_coord (A B : Code) :
    right pe A B ≫ (sumIso (Seed[pe]) A.ty B.ty).hom = coprod.inr := by
  have h := congrArg ((projection (Seed[pe])).map) (Region.Paper.TypeCategory.sumCofan_inr (Φ := Ops) A.ty B.ty)
  change (sumCofan (Seed[pe]) A.ty B.ty).inr = right pe A B at h
  rw [← h, sumCofan_inr_sumIso_hom]

theorem left_inv (A B : Code) :
    (coprod.inl : Obj A.ty ⟶ Obj A.ty ⨿ Obj B.ty) ≫ (sumIso (Seed[pe]) A.ty B.ty).inv = left pe A B := by
  rw [← left_coord pe A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem right_inv (A B : Code) :
    (coprod.inr : Obj B.ty ⟶ Obj A.ty ⨿ Obj B.ty) ≫ (sumIso (Seed[pe]) A.ty B.ty).inv = right pe A B := by
  rw [← right_coord pe A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]

local notation "lit[" c "," x "]" => (Step.lit (F := F) (O := c) x)

theorem lit_left (I A B : Code) (x : A.Value) :
    (lit[A,x] : Step F I A).arrow pe ≫ left pe A B =
      (lit[.sum A B, .inl x] : Step F I (.sum A B)).arrow pe := by
  exact exact_comp pe ((lit[A,x] : Step F I A).typed []) (leftTag A B)
    ((lit[.sum A B, .inl x] : Step F I (.sum A B)).typed [])

theorem lit_right (I A B : Code) (x : B.Value) :
    (lit[B,x] : Step F I B).arrow pe ≫ right pe A B =
      (lit[.sum A B, .inr x] : Step F I (.sum A B)).arrow pe := by
  exact exact_comp pe ((lit[B,x] : Step F I B).typed []) (rightTag A B)
    ((lit[.sum A B, .inr x] : Step F I (.sum A B)).typed [])

/-- Rewriting the typed returned constructor at every leaf postcomposes
the row arrow. The request and selector structure are untouched. -/
theorem mapOut_arrow (s : Step F I O) (f : O.Value → P.Value) (g : Obj O.ty ⟶ Obj P.ty)
    (leaf : ∀ (C : Code) x, (lit[O,x] : Step F C O).arrow pe ≫ g =
      (lit[P,f x] : Step F C P).arrow pe) :
    (Step.mapOut f s).arrow pe = s.arrow pe ≫ g := by
  induction s with
  | lit x => exact (leaf _ x).symm
  | call op x k ih => rw [Step.mapOut, call_arrow, call_arrow, ih f g leaf, Category.assoc]
  | @split A B C l r il ir =>
    apply (cancel_epi (sumIso (Seed[pe]) A.ty B.ty).inv).mp
    rw [Step.mapOut, split_arrow, ← Category.assoc, split_arrow, coprod.desc_comp, il f g leaf, ir f g leaf]

theorem literal_map (c : Code) (f : O.Value → P.Value) (xs : c.Value → O.Value) :
    Step.mapOut f (literals (F := F) c xs) = literals c (fun v => f (xs v)) := by
  simp only [literals, tabulate_map, Step.mapOut]

theorem literals_id (c : Code) :
    (literals (F := F) c (O := c) id).arrow pe = 𝟙 (Obj c.ty) := by
  induction c with
  | unit =>
    exact unit_eta_of_include (Seed[pe]) (fun h => .inl (.inl (.inr h)))
  | sum A B il ir =>
    have leftEq : (literals (F := F) A (O := .sum A B) Sum.inl).arrow pe = left pe A B := by
      have h := mapOut_arrow pe (literals (F := F) A (O := A) id)
        (P := .sum A B) Sum.inl (left pe A B) (fun C x => lit_left pe C A B x)
      rw [literal_map, il, Category.id_comp] at h
      exact h
    have rightEq : (literals (F := F) B (O := .sum A B) Sum.inr).arrow pe = right pe A B := by
      have h := mapOut_arrow pe (literals (F := F) B (O := B) id)
        (P := .sum A B) Sum.inr (right pe A B) (fun C x => lit_right pe C A B x)
      rw [literal_map, ir, Category.id_comp] at h
      exact h
    apply (cancel_epi (sumIso (Seed[pe]) A.ty B.ty).inv).mp
    change (sumIso (Seed[pe]) A.ty B.ty).inv ≫
      (Step.split (literals A (O := .sum A B) Sum.inl) (literals B (O := .sum A B) Sum.inr)).arrow pe = _
    rw [split_arrow, leftEq, rightEq]
    change _ = (sumIso (Seed[pe]) A.ty B.ty).inv ≫ 𝟙 (Obj (Silmaril.coprod A.ty B.ty))
    rw [Category.comp_id]
    apply coprod.hom_ext
    · rw [coprod.inl_desc, left_inv]
    · rw [coprod.inr_desc, right_inv]

omit [HasEff (Opcode F) ε] in
theorem fused_source (first : Ops) (argument : first.argCode.Value)
    (next : first.replyCode.Value → Row F U O) :
    (fused first argument next).source = (plans first argument next).source := by
  simp [fused, plans, replyStep, Step.source, tabulate_source, row_source, Plans.source, Code.dispatch, Plan.source]

omit [HasEff (Opcode F) ε] in
theorem expanded_source (first : Ops) (argument : first.argCode.Value)
    (next : first.replyCode.Value → Row F U O) :
    (expanded first argument next).source = (plans first argument next).expand.source := by
  have h : Step.mapOut (F := F) (O := .sum O U) (P := .sum O (.sum U first.replyCode)) (Sum.map id Sum.inl)
        (replyStep first next) =
      tabulate first.replyCode (fun r => row ((next r).map (T := .sum U first.replyCode) Sum.inl) U) := by
    unfold replyStep
    rw [tabulate_map]
    congr 1
    funext r
    exact row_map (next r) U (K := .sum U first.replyCode) Sum.inl
  simp [expanded, h, Step.source, literals, tabulate_source, row_source, Heterogeneous.Table.source,
    Plans.expand, Plan.expandFirst, Plan.second, Plan.replyCode, Plans.pending, plans,
    Code.dependent, Code.dispatch, Code.encode, Code.decode, Row.source, replySource]
  exact ⟨rfl, rfl⟩

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns (requestBlocks iterateChosen_requestBlocks)

theorem lift_control (S R B : Code) (s : Step F I (.sum B S)) :
    (Step.mapOut (O := .sum B S) (P := .sum B (.sum S R)) (Sum.map id Sum.inl) s).arrow pe ≫
      (sumIso (Seed[pe]) B.ty (.sum S R : Code).ty).hom =
    s.arrow pe ≫ (sumIso (Seed[pe]) B.ty S.ty).hom ≫ coprod.map (𝟙 (Obj B.ty)) (left pe S R) := by
  let newIso := sumIso (Seed[pe]) B.ty (.sum S R : Code).ty
  let oldIso := sumIso (Seed[pe]) B.ty S.ty
  let g := oldIso.hom ≫ coprod.map (𝟙 (Obj B.ty)) (left pe S R) ≫ newIso.inv
  have h := mapOut_arrow pe s (P := .sum B (.sum S R)) (Sum.map id Sum.inl) g (fun C v => ?_)
  · rw [h]
    change (s.arrow pe ≫ oldIso.hom ≫ coprod.map (𝟙 (Obj B.ty)) (left pe S R) ≫ newIso.inv) ≫ newIso.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  · cases v with
    | inl b =>
      change (lit[.sum B S, .inl b] : Step F C (.sum B S)).arrow pe ≫
        (oldIso.hom ≫ coprod.map (𝟙 (Obj B.ty)) (left pe S R) ≫ newIso.inv) = _
      rw [← lit_left pe C B S b, Category.assoc, ← Category.assoc (left pe B S), left_coord,
        coprod.inl_map_assoc, Category.id_comp, left_inv, lit_left]
      rfl
    | inr u =>
      change (lit[.sum B S, .inr u] : Step F C (.sum B S)).arrow pe ≫
        (oldIso.hom ≫ coprod.map (𝟙 (Obj B.ty)) (left pe S R) ≫ newIso.inv) = _
      rw [← lit_right pe C B S u, Category.assoc, ← Category.assoc (right pe B S), right_coord,
        coprod.inr_map_assoc, right_inv, ← Category.assoc, lit_left, lit_right]
      rfl

private theorem pending_encode (S R B : Code) :
    (literals (F := F) R (O := .sum B (.sum S R)) (fun v => .inr (.inr v))).arrow pe =
      right pe S R ≫ right pe B (.sum S R) := by
  have h := mapOut_arrow pe (literals (F := F) R (O := R) id) (P := .sum B (.sum S R))
    (fun v => .inr (.inr v)) (right pe S R ≫ right pe B (.sum S R)) (fun C v => by
      rw [← Category.assoc, lit_right, lit_right])
  rw [literal_map, literals_id, Category.id_comp] at h
  exact h

private theorem expanded_coords (first : Ops) (argument : first.argCode.Value)
    (next : first.replyCode.Value → Row F U O) :
    (sumIso (Seed[pe]) Code.unit.ty first.replyCode.ty).inv ≫
      (expanded first argument next).arrow pe ≫
        (sumIso (Seed[pe]) O.ty (.sum U first.replyCode : Code).ty).hom =
      requestBlocks pe (request (I := U) pe first argument)
        ((replyStep first next).arrow pe ≫ (sumIso (Seed[pe]) O.ty Code.unit.ty).hom) ≫
          (coprod.associator (Obj O.ty) (Obj Code.unit.ty) (Obj first.replyCode.ty)).hom ≫
            coprod.map (𝟙 (Obj O.ty)) (sumIso (Seed[pe]) Code.unit.ty first.replyCode.ty).inv := by
  rw [← Category.assoc, expanded, split_arrow, coprod.desc_comp]
  apply coprod.hom_ext
  · simp only [coprod.inl_desc, requestBlocks, Category.assoc, coprod.inl_desc_assoc]
    simp only [call_arrow, pending_encode, Category.assoc, right_coord]
    simp [coprod.associator, Category.assoc]
    change _ = request (I := U) pe first argument ≫
      (coprod.inr : Obj first.replyCode.ty ⟶ Obj Code.unit.ty ⨿ Obj first.replyCode.ty) ≫
        (sumIso (Seed[pe]) Code.unit.ty first.replyCode.ty).inv ≫ coprod.inr
    rw [← Category.assoc (coprod.inr : Obj first.replyCode.ty ⟶ Obj Code.unit.ty ⨿ Obj first.replyCode.ty), right_inv]
    rfl
  · simp only [coprod.inr_desc, requestBlocks, Category.assoc, coprod.inr_desc_assoc]
    rw [lift_control]
    congr 2
    apply coprod.hom_ext
    · simp [coprod.associator]
      rfl
    · simp [coprod.associator, Category.assoc]
      change _ = (coprod.inl : Obj Code.unit.ty ⟶ Obj Code.unit.ty ⨿ Obj first.replyCode.ty) ≫
        (sumIso (Seed[pe]) Code.unit.ty first.replyCode.ty).inv ≫ coprod.inr
      rw [← Category.assoc, left_inv]
      rfl

open Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory (iterateRegion iterateRegion_valueBranches)

theorem loop_coords (s : Step F I (.sum O I)) :
    iterateChosen (Seed[pe]) (s.arrow pe ≫ (sumIso (Seed[pe]) O.ty I.ty).hom) =
      ofRegion (Seed[pe]) (iterateRegion_valueBranches (s.typed [])) := by
  change iterateSum (Seed[pe])
    ((s.arrow pe ≫ (sumIso (Seed[pe]) O.ty I.ty).hom) ≫ (sumIso (Seed[pe]) O.ty I.ty).inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold Step.arrow
  rw [iterateSum_map, Region.Paper.TypeCategory.iterateSum_ofRegion]

/-- The literal typed CFG for the original loop equals the pending-state
CFG entered from the initializer translated into its left summand. -/
private theorem joined_loop (first : Ops) (argument : first.argCode.Value) (next : first.replyCode.Value → Row F U O) :
    ofRegion (Seed[pe]) (iterateRegion_valueBranches ((fused first argument next).typed [])) =
      left pe U first.replyCode ≫
        ofRegion (Seed[pe]) (iterateRegion_valueBranches ((expanded first argument next).typed [])) := by
  rw [← loop_coords, ← loop_coords, fused, call_arrow, Category.assoc, iterateChosen_requestBlocks]
  let compare := sumIso (Seed[pe]) Code.unit.ty first.replyCode.ty
  have eq := uniformity_of_iso (Seed[pe]) compare.symm
    (requestBlocks pe (request (I := U) pe first argument)
      ((replyStep first next).arrow pe ≫ (sumIso (Seed[pe]) O.ty Code.unit.ty).hom) ≫
      (coprod.associator (Obj O.ty) (Obj Code.unit.ty) (Obj first.replyCode.ty)).hom)
    ((expanded first argument next).arrow pe ≫ (sumIso (Seed[pe]) O.ty (.sum U first.replyCode : Code).ty).hom)
    (by
      change (_ ≫ _) ≫ coprod.map (𝟙 (Obj O.ty)) compare.inv = compare.inv ≫ _ ≫ _
      rw [Category.assoc]
      exact (expanded_coords pe first argument next).symm)
  rw [eq, ← Category.assoc]
  congr 1
  exact left_inv pe U first.replyCode

end Category

open Silmaril.Isotope.LetIter.LocallyNameless (HasTypeEffect AbortEquiv)
open Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory (iterateRegion iterateRegion_valueBranches)

theorem nativeValue_lowers (c : Code) (x : c.Value) (m : Nat) :
    (c.literal x).toLetIter m = some (nativeValue (F := F) m c x) := by
  induction c with
  | unit => rfl
  | sum l r il ir => cases x <;> simp [Code.literal, Expr.toLetIter, nativeValue, il, ir]

theorem Step.lowers (s : Step F I O) (m : Nat) :
    s.source.toLetIter (m+1) = some (s.native m) := by
  induction s generalizing m with
  | lit x => exact nativeValue_lowers _ x _
  | call f x k ih =>
    simp [Step.source, Step.native, Expr.toLetIter, nativeValue_lowers, ih]
  | split l r il ir =>
    simp [Step.source, Step.native, Expr.toLetIter, il, ir]

theorem value_erase (c : Code) (x : c.Value) (m : Nat) :
    eraseValue (nativeValue (F := F) m c x) = some (value c x) := by
  induction c with
  | unit => rfl
  | sum l r il ir => cases x <;> simp [nativeValue, eraseValue, value, il, ir]

private theorem value_step (c : Code) (x : c.Value) (m : Nat) :
    eraseStep (nativeValue (F := F) m c x) = some (.br 0 (value c x)) := by
  cases c with
  | unit => rfl
  | sum l r =>
    cases x <;> simp [nativeValue, eraseStep, eraseValue, value, value_erase]

theorem Step.erases (s : Step F I O) (m : Nat) :
    eraseStep (s.native m) = some s.ssa := by
  induction s generalizing m with
  | lit x => exact value_step _ x _
  | call f x k ih => simp [Step.native, Step.ssa, eraseStep, eraseValue, value_erase, ih]
  | split l r il ir => simp [Step.native, Step.ssa, eraseStep, eraseValue, il, ir]

theorem erase_loop (s : Step F I (.sum O I)) (v : I.Value) :
    eraseLoop I (.iter (nativeValue 0 I v) (s.native 0)) = some (loopCFG s v) := by
  simp [eraseLoop, value_step, Step.erases s, loopCFG]

theorem loopCFG_typed (s : Step F I (.sum O I)) (v : I.Value) :
    Region.ValueBranches [Code.unit.ty] (loopCFG s v) [O.ty] :=
  Region.CfgEta.TypeCategory.seqValueBranches ((Step.lit (I := U) (O := I) v : Step F U I).typed [])
    (iterateRegion_valueBranches (s.typed []))

section AtBound

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

omit [EffectIteration ε] in
theorem Step.wf (s : Step F I O) {Γ : EffectCtx (Ty Unit) ε} (hf : ∀ f : Ops, instrEff f ≤ e) :
    Wf ((I.ty, ⊥) :: Γ) s.source O.ty e := by
  induction s generalizing Γ with
  | lit x => exact literal_wf _ x
  | call f x k ih => exact .let₁ (.op (hf f) (literal_wf _ x)) ih
  | split l r il ir => exact .case (.var 0 bot_le) il ir

local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

theorem typed_loop (s : Step F I (.sum O I)) (v : I.Value) (hf : ∀ f : Ops, instrEff f ≤ e)
    (he : IsIterative e) :
    HasTypeEffect Free .nil (.iter (nativeValue 0 I v) (s.native 0)) O.ty e := by
  have base : Wf ([] : EffectCtx (Ty Unit) ε) (I.literal v : Expr Ops) I.ty e := literal_wf I v
  obtain ⟨_, hinit, ta⟩ := base.toLetIter
  obtain ⟨_, hbody, tb⟩ := (Step.wf s (Γ := []) hf).toLetIter
  exact .iter he ((Option.some.inj (hinit.symm.trans (nativeValue_lowers I v 0))) ▸ ta)
    ((Option.some.inj (hbody.symm.trans (Step.lowers s 0))) ▸ tb)

omit [EffectIteration ε] in
theorem fused_lowers (f : Ops) (x : f.argCode.Value) (k : f.replyCode.Value → Row F U O) :
    (plans f x k).source.toLetIter 1 = some ((fused f x k).native 0) :=
  (fused_source f x k) ▸ Step.lowers (fused f x k) 0

omit [EffectIteration ε] in
theorem expanded_lowers (f : Ops) (x : f.argCode.Value) (k : f.replyCode.Value → Row F U O) :
    (plans f x k).expand.source.toLetIter 1 = some ((expanded f x k).native 0) :=
  (expanded_source f x k) ▸ Step.lowers (expanded f x k) 0

omit [EffectIteration ε] in
theorem native_expansion (f : Ops) (x : f.argCode.Value) (k : f.replyCode.Value → Row F U O) :
    AbortEquiv (⊥ : ε) Free .nil (fusedNative f x k) (expandedNative f x k) O.ty :=
  Plans.expand_eq (plans f x k) PUnit.unit rfl (fused_lowers f x k) rfl (expanded_lowers f x k)

omit [EffectIteration ε] in
theorem joined_endpoints (f : Ops) (x : f.argCode.Value) (k : f.replyCode.Value → Row F U O) :
    Region.Paper.Extension.Eqv (Seed[(⊥ : ε)]) [Code.unit.ty]
      (loopCFG (fused f x k) PUnit.unit) (loopCFG (expanded f x k) (.inl PUnit.unit)) [O.ty] := by
  let pe : ε := ⊥
  let original := fused f x k
  let expansion := expanded f x k
  have src := loopCFG_typed original PUnit.unit
  have tgt := loopCFG_typed expansion (.inl PUnit.unit)
  apply (ofRegion_eq_iff (Seed[pe]) src tgt).mp
  rw [← exact_comp pe ((Step.lit (F := F) (I := U) (O := U) PUnit.unit).typed [])
    (iterateRegion_valueBranches (original.typed [])) src,
    ← exact_comp pe ((Step.lit (F := F) (I := U) (O := .sum U f.replyCode) (.inl PUnit.unit)).typed [])
    (iterateRegion_valueBranches (expansion.typed [])) tgt]
  have init : (Step.lit (F := F) (I := U) (O := U) PUnit.unit).arrow pe = 𝟙 (ofType (Seed[pe]) Code.unit.ty) :=
    literals_id pe U
  change (Step.lit (F := F) (I := U) (O := U) PUnit.unit).arrow pe ≫ _ =
    (Step.lit (F := F) (I := U) (O := .sum U f.replyCode) (.inl PUnit.unit)).arrow pe ≫ _
  rw [← lit_left pe U U f.replyCode PUnit.unit, init, Category.id_comp, Category.id_comp]
  exact joined_loop pe f x k

/-- The computed #3846 native endpoints have the supplied effect bound,
are related by native AbortEquiv, and erase to equal typed LambdaSSA CFGs. -/
theorem endpoint_transport (f : Ops) (x : f.argCode.Value) (k : f.replyCode.Value → Row F U O)
    (hf : ∀ p : Ops, instrEff p ≤ e) (he : IsIterative e) :
    HasTypeEffect Free .nil (fusedNative f x k) O.ty e ∧
    HasTypeEffect Free .nil (expandedNative f x k) O.ty e ∧
    AbortEquiv (⊥ : ε) Free .nil (fusedNative f x k) (expandedNative f x k) O.ty ∧
    ∃ (r s : Region Ops), eraseLoop U (fusedNative f x k) = some r ∧
      eraseLoop (.sum U f.replyCode) (expandedNative f x k) = some s ∧
      Region.ValueBranches [Code.unit.ty] r [O.ty] ∧ Region.ValueBranches [Code.unit.ty] s [O.ty] ∧
      Region.Paper.Extension.Eqv (Seed[(⊥ : ε)]) [Code.unit.ty] r s [O.ty] := by
  exact ⟨typed_loop (fused f x k) PUnit.unit hf he, typed_loop (expanded f x k) (.inl PUnit.unit) hf he,
    native_expansion f x k, _, _, erase_loop (fused f x k) PUnit.unit,
    erase_loop (expanded f x k) (.inl PUnit.unit), loopCFG_typed _ _, loopCFG_typed _ _, joined_endpoints f x k⟩

end AtBound

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Proofs
