module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Mixed.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlockTransport
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Transfer.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Proofs.Transfer

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Transfer
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S B I O P J : Code}

local notation "Ops" => Opcode F
local notation "U" => Code.unit

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
open Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory (iterateRegion_valueBranches)
open Silmaril.Isotope.LetIter.LocallyNameless (HasTypeEffect AbortEquiv)

set_option backward.isDefEq.respectTransparency false

private theorem lower_let_ne_inr (a b : Expr Ops) (m : Nat) (v : NTm F m) :
    (Expr.let₁ a b).toLetIter m ≠ some (.inr v) := by
  cases l : a.toLetIter m <;> cases r : b.toLetIter (m+1) <;> simp [Expr.toLetIter, l, r]

/-- An original row in the #3846 renderer never lowers to a bare pure repeat. -/
private theorem no_bare_transfer (p : Plan F S B) (m : Nat) (v : NTm F m) :
    p.source.toLetIter m ≠ some (.inr v) := by
  cases p with
  | two f x k => exact lower_let_ne_inr _ _ m v
  | one r =>
    cases r with
    | call f x k => exact lower_let_ne_inr _ _ m v
    | ret b =>
      cases h : (B.literal b : Expr Ops).toLetIter m <;> simp [Plan.source, Row.source, Expr.toLetIter, h]

theorem mapOut_map {Q : Code} (s : Step F I O) (f : O.Value → P.Value) (g : P.Value → Q.Value) :
    Step.mapOut g (Step.mapOut f s) = Step.mapOut (fun x => g (f x)) s := by
  induction s with
  | lit x => rfl
  | call op x k ih => simp [Step.mapOut, ih]
  | split l r il ir => simp [Step.mapOut, il, ir]

theorem Rows.firstMap_mapOut {Q : Code} (t : Rows F S B I) (done : (Code.sum B S).Value → P.Value)
    (pending : t.pending.Value → P.Value) (f : P.Value → Q.Value) :
    Step.mapOut f (t.firstMap done pending) = t.firstMap (fun x => f (done x)) (fun x => f (pending x)) := by
  induction t with
  | leaf p =>
    cases p with
    | transfer target => rfl
    | ordinary p =>
      cases p with
      | one r => exact mapOut_map (row r U) done f
      | two op x k =>
        simp [Rows.firstMap, Step.mapOut, literal_map]
        rfl
  | split l r il ir =>
    simp [Rows.firstMap, Step.mapOut, il, ir]

theorem Rows.fused_source (t : Rows F S B I) :
    t.fused.source = I.dispatch (fun v => (t.plans v).source) (.var 0) := by
  induction t with
  | leaf p =>
    cases p with
    | transfer target => rfl
    | ordinary p =>
      cases p with
      | one r => exact row_source r U
      | two f x k =>
        simp [Rows.fused, Rows.plans, Step.source, tabulate_source, row_source, Code.dispatch, TransferPlan.source, Plan.source]
  | split l r il ir =>
    simp [Rows.fused, Step.source, Code.dispatch, Rows.plans, il, ir]

private def firstSource (done : (Code.sum B S).Value → O.Value) :
    (p : TransferPlan F S B) → (p.replyCode.Value → O.Value) → Expr Ops
  | .ordinary (.one r), _ => (Step.mapOut done (row r U)).source
  | .ordinary (.two f x _), pending => .let₁ (.op f (f.argCode.literal x))
      (f.replyCode.dispatch (fun r => O.literal (pending r)) (.var 0))
  | .transfer target, _ => O.literal (done (.inr target))

private theorem Rows.firstMap_source (t : Rows F S B I) (done : (Code.sum B S).Value → O.Value)
    (pending : t.pending.Value → O.Value) :
    (t.firstMap done pending).source =
      I.dispatch (fun v => firstSource done (t.plans v)
        (fun r => pending (Code.encode I (fun s => (t.plans s).replyCode) v r))) (.var 0) := by
  induction t with
  | leaf p =>
    cases p with
    | transfer target => rfl
    | ordinary p =>
      cases p with
      | one r => rfl
      | two f x k =>
        simp [Rows.firstMap, Rows.plans, Step.source, literals, tabulate_source, Code.dispatch, Code.encode, firstSource]
  | split l r il ir =>
    simp [Rows.firstMap, Step.source, Code.dispatch, Rows.plans, Code.encode, il, ir]

theorem Rows.second_map_source (t : Rows F S B I) (inject : S.Value → J.Value) :
    (Step.mapOut (O := .sum B S) (P := .sum B J) (Sum.map id inject) t.second).source =
      t.pending.dispatch (fun w =>
        let p := Code.decode I (fun v => (t.plans v).replyCode) w
        (((t.plans p.1).second p.2).map inject).source) (.var 0) := by
  induction t with
  | leaf p =>
    cases p with
    | transfer target => rfl
    | ordinary p =>
      cases p with
      | one r =>
        change (Step.mapOut (O := .sum B S) (P := .sum B J) (Sum.map id inject) (row r U)).source =
          (r.map inject).source
        rw [row_map r U inject, row_source]
      | two f x k =>
        change (Step.mapOut (O := .sum B S) (P := .sum B J) (Sum.map id inject)
          (tabulate f.replyCode (fun v => row (k v) U))).source =
            f.replyCode.dispatch (fun w => ((k w).map inject).source) (.var 0)
        rw [tabulate_map, tabulate_source]
        apply congrArg (fun leaves => f.replyCode.dispatch leaves (.var 0))
        funext w
        rw [row_map (k w) U inject, row_source]
  | split l r il ir =>
    rw [Rows.second, Step.mapOut, Step.source, il, ir]
    rfl

private theorem firstSource_expanded (p : TransferPlan F S B) (encode : p.replyCode.Value → J.Value) :
    firstSource (S := S) (B := B) (O := .sum B (.sum S J)) (Sum.map id Sum.inl) p
      (fun v => .inr (.inr (encode v))) = (p.expandFirst J encode).source := by
  cases p with
  | transfer target => rfl
  | ordinary p =>
    cases p with
    | one r => exact (congrArg Step.source (row_map r U (K := .sum S J) Sum.inl)).trans (row_source _ U)
    | two f x k => rfl

theorem Rows.expanded_source (t : Rows F S B S) :
    t.expanded.source = (TransferPlans.expand t.plans).source := by
  rw [Rows.expanded, Step.source, Rows.firstMap_source t
    (O := .sum B (.sum S t.pending)) (Sum.map id Sum.inl),
    Rows.second_map_source (J := .sum S t.pending) t Sum.inl, TransferTable.source, Code.dispatch]
  congr 1
  apply congrArg (fun rows => S.dispatch rows (.var 0))
  funext v
  exact firstSource_expanded (t.plans v) (Code.encode S (fun s => (t.plans s).replyCode) v)

variable {ε : Type} [HasEff (Opcode F) ε]

variable {ε : Type} [HasEff (Opcode F) ε]

set_option hygiene false in
local notation "Seed[" p "]" => targetSeed (F := F) (ε := ε) p

section Category

variable (pe : ε)

set_option hygiene false in
local notation "Obj" => ofType (Seed[pe])

local notation "lit[" c "," x "]" => (Step.lit (F := F) (O := c) x)

private noncomputable def pairCase {A C D : Code} (f : Obj A.ty ⟶ Obj D.ty) (g : Obj C.ty ⟶ Obj D.ty) :
    Obj (.sum A C : Code).ty ⟶ Obj D.ty :=
  (sumIso (Seed[pe]) A.ty C.ty).hom ≫ coprod.desc f g

private theorem left_case {A C D : Code} (f : Obj A.ty ⟶ Obj D.ty) (g : Obj C.ty ⟶ Obj D.ty) :
    left pe A C ≫ pairCase pe (A := A) (C := C) (D := D) f g = f := by
  rw [← left_inv, Category.assoc, pairCase, Iso.inv_hom_id_assoc, coprod.inl_desc]

private theorem right_case {A C D : Code} (f : Obj A.ty ⟶ Obj D.ty) (g : Obj C.ty ⟶ Obj D.ty) :
    right pe A C ≫ pairCase pe (A := A) (C := C) (D := D) f g = g := by
  rw [← right_inv, Category.assoc, pairCase, Iso.inv_hom_id_assoc, coprod.inr_desc]

private theorem case_comp {A C D E : Code} (f : Obj A.ty ⟶ Obj D.ty) (g : Obj C.ty ⟶ Obj D.ty)
    (h : Obj D.ty ⟶ Obj E.ty) :
    pairCase pe (A := A) (C := C) (D := D) f g ≫ h = pairCase pe (A := A) (C := C) (D := E) (f ≫ h) (g ≫ h) := by
  simp only [pairCase, Category.assoc, coprod.desc_comp]

private theorem split_left (l : Step F I O) (r : Step F J O) :
    left pe I J ≫ (Step.split l r).arrow pe = l.arrow pe := by
  rw [← left_inv, Category.assoc, split_arrow, coprod.inl_desc]

private theorem split_right (l : Step F I O) (r : Step F J O) :
    right pe I J ≫ (Step.split l r).arrow pe = r.arrow pe := by
  rw [← right_inv, Category.assoc, split_arrow, coprod.inr_desc]

private noncomputable def finish (t : Rows F S B I) :
    Obj (.sum (.sum B S) t.pending : Code).ty ⟶ Obj (.sum B S : Code).ty :=
  pairCase pe (A := .sum B S) (C := t.pending) (D := .sum B S) (𝟙 _) (t.second.arrow pe)

private theorem literal_case {A C D : Code}
    (f : Obj A.ty ⟶ Obj D.ty) (g : Obj C.ty ⟶ Obj D.ty)
    (leftVal : A.Value → D.Value) (rightVal : C.Value → D.Value)
    (fl : ∀ (X : Code) x, (lit[A,x] : Step F X A).arrow pe ≫ f = (lit[D,leftVal x] : Step F X D).arrow pe)
    (fr : ∀ (X : Code) x, (lit[C,x] : Step F X C).arrow pe ≫ g = (lit[D,rightVal x] : Step F X D).arrow pe)
    (X : Code) (v : (Code.sum A C).Value) :
    (lit[.sum A C,v] : Step F X (.sum A C)).arrow pe ≫ pairCase pe (A := A) (C := C) (D := D) f g =
      (lit[D,Sum.elim leftVal rightVal v] : Step F X D).arrow pe := by
  cases v with
  | inl x => rw [← lit_left pe X A C x, Category.assoc, left_case, fl]; rfl
  | inr x => rw [← lit_right pe X A C x, Category.assoc, right_case, fr]; rfl

private theorem first_tag (t : Rows F S B I) (done : (Code.sum B S).Value → O.Value)
    (pending : t.pending.Value → O.Value)
    (l : Obj (.sum B S : Code).ty ⟶ Obj O.ty) (r : Obj t.pending.ty ⟶ Obj O.ty)
    (fl : ∀ (X : Code) x, (lit[.sum B S,x] : Step F X (.sum B S)).arrow pe ≫ l =
      (lit[O,done x] : Step F X O).arrow pe)
    (fr : ∀ (X : Code) x, (lit[t.pending,x] : Step F X t.pending).arrow pe ≫ r =
      (lit[O,pending x] : Step F X O).arrow pe) :
    (t.firstMap done pending).arrow pe = t.first.arrow pe ≫
      pairCase pe (A := .sum B S) (C := t.pending) (D := O) l r := by
  have eq := mapOut_arrow pe t.first (P := O) (Sum.elim done pending)
    (pairCase pe (A := .sum B S) (C := t.pending) (D := O) l r)
    (literal_case pe (A := .sum B S) (C := t.pending) (D := O) l r done pending fl fr)
  rw [Rows.first, Rows.firstMap_mapOut] at eq
  exact eq

private theorem finish_left (t : Rows F S B I) :
    left pe (.sum B S) t.pending ≫ finish pe t = 𝟙 _ :=
  left_case pe (A := .sum B S) (C := t.pending) (D := .sum B S) (𝟙 _) (t.second.arrow pe)

private theorem finish_right (t : Rows F S B I) :
    right pe (.sum B S) t.pending ≫ finish pe t = t.second.arrow pe :=
  right_case pe (A := .sum B S) (C := t.pending) (D := .sum B S) (𝟙 _) (t.second.arrow pe)

private theorem factor (t : Rows F S B I) :
    t.first.arrow pe ≫ finish pe t = t.fused.arrow pe := by
  induction t with
  | leaf p =>
    cases p with
    | transfer target =>
      change (lit[.sum (.sum B S) U, .inl (.inr target)] : Step F U (.sum (.sum B S) U)).arrow pe ≫
        finish pe (Rows.leaf (.transfer target)) =
          (lit[.sum B S, .inr target] : Step F U (.sum B S)).arrow pe
      rw [← lit_left pe U (.sum B S) U (.inr target), Category.assoc]
      let t : Rows F S B U := .leaf (.transfer target)
      change (lit[.sum B S, .inr target] : Step F U (.sum B S)).arrow pe ≫
        left pe (.sum B S) t.pending ≫ finish pe t = _
      rw [finish_left, Category.comp_id]
    | ordinary p =>
      cases p with
      | one r =>
        change (Step.mapOut (O := .sum B S) (P := .sum (.sum B S) U) Sum.inl (row r U)).arrow pe ≫
          finish pe (Rows.leaf (.ordinary (.one r))) = (row r U).arrow pe
        rw [mapOut_arrow pe _ _ (left pe (.sum B S) U) (fun X x => lit_left pe X (.sum B S) U x),
          Category.assoc]
        change (row r U).arrow pe ≫ left pe (.sum B S) (Rows.leaf (.ordinary (.one r))).pending ≫
          finish pe (Rows.leaf (.ordinary (.one r))) = _
        rw [finish_left, Category.comp_id]
      | two f x k =>
        have lit_eq := mapOut_arrow pe (literals (F := F) f.replyCode (O := f.replyCode) id)
          (P := .sum (.sum B S) f.replyCode) Sum.inr (right pe (.sum B S) f.replyCode)
          (fun X w => lit_right pe X (.sum B S) f.replyCode w)
        rw [literal_map, literals_id, Category.id_comp] at lit_eq
        change (Step.call (I := U) f x (literals f.replyCode (O := .sum (.sum B S) f.replyCode) Sum.inr)).arrow pe ≫
          finish pe (Rows.leaf (.ordinary (.two f x k))) = (Rows.fused (Rows.leaf (.ordinary (.two f x k)))).arrow pe
        rw [call_arrow]
        change (request (I := U) pe f x ≫ (literals f.replyCode (O := .sum (.sum B S) f.replyCode)
          (fun v => .inr (id v))).arrow pe) ≫ finish pe (Rows.leaf (.ordinary (.two f x k))) = _
        rw [lit_eq, Category.assoc]
        change request (I := U) pe f x ≫ right pe (.sum B S) (Rows.leaf (.ordinary (.two f x k))).pending ≫
          finish pe (Rows.leaf (.ordinary (.two f x k))) = _
        rw [finish_right, Rows.fused, call_arrow, Rows.second]
  | @split L R l r il ir =>
    let C := Code.sum B S
    let D := Code.sum l.pending r.pending
    have lmap : (l.firstMap (O := .sum C D) Sum.inl (fun v => .inr (.inl v))).arrow pe =
        l.first.arrow pe ≫ pairCase pe (A := C) (C := l.pending) (D := .sum C D)
          (left pe C D) (left pe l.pending r.pending ≫ right pe C D) := by
      apply first_tag
      · exact fun X v => lit_left pe X C D v
      · intro X v
        rw [← Category.assoc, lit_left, lit_right]
    have rmap : (r.firstMap (O := .sum C D) Sum.inl (fun v => .inr (.inr v))).arrow pe =
        r.first.arrow pe ≫ pairCase pe (A := C) (C := r.pending) (D := .sum C D)
          (left pe C D) (right pe l.pending r.pending ≫ right pe C D) := by
      apply first_tag
      · exact fun X v => lit_left pe X C D v
      · intro X v
        rw [← Category.assoc, lit_right, lit_right]
    have leftPass : left pe C D ≫ finish pe (.split l r) = 𝟙 _ := finish_left pe (.split l r)
    have rightPass : right pe C D ≫ finish pe (.split l r) = (Step.split l.second r.second).arrow pe :=
      finish_right pe (.split l r)
    apply (cancel_epi (sumIso (Seed[pe]) L.ty R.ty).inv).mp
    rw [Rows.fused, split_arrow, ← Category.assoc, Rows.first, Rows.firstMap, split_arrow]
    apply coprod.hom_ext
    · simp only [coprod.inl_desc_assoc, coprod.inl_desc]
      change (l.firstMap (O := .sum C D) Sum.inl (fun v => .inr (.inl v))).arrow pe ≫ finish pe (.split l r) = _
      rw [lmap, Category.assoc, case_comp, leftPass, Category.assoc, rightPass, split_left]
      exact il
    · simp only [coprod.inr_desc_assoc, coprod.inr_desc]
      change (r.firstMap (O := .sum C D) Sum.inl (fun v => .inr (.inr v))).arrow pe ≫ finish pe (.split l r) = _
      rw [rmap, Category.assoc, case_comp, leftPass, Category.assoc, rightPass, split_right]
      exact ir

private noncomputable def firstArrow (t : Rows F S B I) :
    Obj I.ty ⟶ (Obj B.ty ⨿ Obj S.ty) ⨿ Obj t.pending.ty :=
  t.first.arrow pe ≫ (sumIso (Seed[pe]) (.sum B S : Code).ty t.pending.ty).hom ≫
    coprod.map (sumIso (Seed[pe]) B.ty S.ty).hom (𝟙 _)

private noncomputable def secondArrow (t : Rows F S B I) :
    Obj t.pending.ty ⟶ Obj B.ty ⨿ Obj S.ty :=
  t.second.arrow pe ≫ (sumIso (Seed[pe]) B.ty S.ty).hom

private theorem fused_coords (t : Rows F S B I) :
    t.fused.arrow pe ≫ (sumIso (Seed[pe]) B.ty S.ty).hom =
      firstArrow pe t ≫ coprod.desc (𝟙 (Obj B.ty ⨿ Obj S.ty)) (secondArrow pe t) := by
  rw [← factor pe t]
  simp only [finish, pairCase, firstArrow, secondArrow, Category.assoc, coprod.desc_comp,
    coprod.map_desc, Category.id_comp, Category.comp_id]

private noncomputable def liftResult (S R B : Code) :
    Obj (.sum B S : Code).ty ⟶ Obj (.sum B (.sum S R) : Code).ty :=
  (sumIso (Seed[pe]) B.ty S.ty).hom ≫ coprod.map (𝟙 _) (left pe S R) ≫
    (sumIso (Seed[pe]) B.ty (.sum S R : Code).ty).inv

private theorem lift_literal (S R B X : Code) (v : (Code.sum B S).Value) :
    (lit[.sum B S,v] : Step F X (.sum B S)).arrow pe ≫ liftResult pe S R B =
      (lit[.sum B (.sum S R), Sum.map id Sum.inl v] : Step F X (.sum B (.sum S R))).arrow pe := by
  apply (cancel_mono (sumIso (Seed[pe]) B.ty (.sum S R : Code).ty).hom).mp
  simp only [liftResult, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (lift_control pe S R B (lit[.sum B S,v] : Step F X (.sum B S))).symm

private theorem first_expanded (t : Rows F S B I) :
    (t.firstMap (O := .sum B (.sum S t.pending)) (Sum.map id Sum.inl) (fun v => .inr (.inr v))).arrow pe =
      t.first.arrow pe ≫ pairCase pe (A := .sum B S) (C := t.pending) (D := .sum B (.sum S t.pending))
        (liftResult pe S t.pending B) (right pe S t.pending ≫ right pe B (.sum S t.pending)) := by
  apply first_tag
  · exact lift_literal pe S t.pending B
  · intro X v
    rw [← Category.assoc, lit_right, lit_right]

private noncomputable def blocks (t : Rows F S B S) :
    Obj S.ty ⨿ Obj t.pending.ty ⟶ (Obj B.ty ⨿ Obj S.ty) ⨿ Obj t.pending.ty :=
  coprod.desc (firstArrow pe t) (secondArrow pe t ≫ coprod.inl)

private theorem flatten_coords (S R B : Code) :
    (coprod.associator (Obj B.ty) (Obj S.ty) (Obj R.ty)).hom ≫
      coprod.map (𝟙 (Obj B.ty)) (sumIso (Seed[pe]) S.ty R.ty).inv =
    coprod.desc (coprod.map (𝟙 (Obj B.ty)) (left pe S R))
      (right pe S R ≫ (coprod.inr : Obj (.sum S R : Code).ty ⟶ Obj B.ty ⨿ Obj (.sum S R : Code).ty)) := by
  apply coprod.hom_ext
  · apply coprod.hom_ext
    · simp [coprod.associator]
      rfl
    · simp [coprod.associator, Category.assoc]
      change (coprod.inl : Obj S.ty ⟶ Obj S.ty ⨿ Obj R.ty) ≫
        (sumIso (Seed[pe]) S.ty R.ty).inv ≫ coprod.inr = _
      rw [← Category.assoc, left_inv]
      rfl
  · simp [coprod.associator, Category.assoc]
    change (coprod.inr : Obj R.ty ⟶ Obj S.ty ⨿ Obj R.ty) ≫
      (sumIso (Seed[pe]) S.ty R.ty).inv ≫ coprod.inr = _
    rw [← Category.assoc, right_inv]
    rfl

private theorem expanded_coords (t : Rows F S B S) :
    (sumIso (Seed[pe]) S.ty t.pending.ty).inv ≫ t.expanded.arrow pe ≫
        (sumIso (Seed[pe]) B.ty (.sum S t.pending : Code).ty).hom =
      blocks pe t ≫ (coprod.associator (Obj B.ty) (Obj S.ty) (Obj t.pending.ty)).hom ≫
        coprod.map (𝟙 (Obj B.ty)) (sumIso (Seed[pe]) S.ty t.pending.ty).inv := by
  rw [← Category.assoc, Rows.expanded, split_arrow, coprod.desc_comp, flatten_coords pe S t.pending B]
  apply coprod.hom_ext
  · simp only [coprod.inl_desc, blocks, Category.assoc, first_expanded, firstArrow,
      pairCase, coprod.desc_comp, coprod.map_desc, liftResult, Iso.inv_hom_id, Category.comp_id,
      right_coord, Category.id_comp]
  · simp only [coprod.inr_desc, blocks, Category.assoc, coprod.inr_desc_assoc]
    rw [lift_control]
    conv_rhs => rw [coprod.inl_desc]
    rw [secondArrow, Category.assoc]

private theorem joined_loop (t : Rows F S B S) :
    ofRegion (Seed[pe]) (iterateRegion_valueBranches (t.fused.typed [])) =
      left pe S t.pending ≫ ofRegion (Seed[pe]) (iterateRegion_valueBranches (t.expanded.typed [])) := by
  rw [← loop_coords, ← loop_coords, fused_coords, iterateChosen_bypass]
  let compare := sumIso (Seed[pe]) S.ty t.pending.ty
  have eq := uniformity_of_iso (Seed[pe]) compare.symm
    (blocks pe t ≫ (coprod.associator (Obj B.ty) (Obj S.ty) (Obj t.pending.ty)).hom)
    (t.expanded.arrow pe ≫ (sumIso (Seed[pe]) B.ty (.sum S t.pending : Code).ty).hom)
    (by
      change (_ ≫ _) ≫ coprod.map (𝟙 (Obj B.ty)) compare.inv = compare.inv ≫ _ ≫ _
      rw [Category.assoc]
      exact (expanded_coords pe t).symm)
  change coprod.inl ≫ iterateChosen (Seed[pe]) (blocks pe t ≫ _) = _
  rw [eq, ← Category.assoc]
  congr 1
  exact left_inv pe S t.pending

theorem joined_endpoints (t : Rows F S B S) (init : S.Value) :
    Region.Paper.Extension.Eqv (Seed[pe]) [Code.unit.ty]
      (loopCFG t.fused init) (loopCFG t.expanded (.inl init)) [B.ty] := by
  have src := loopCFG_typed t.fused init
  have tgt := loopCFG_typed t.expanded (.inl init)
  apply (ofRegion_eq_iff (Seed[pe]) src tgt).mp
  rw [← exact_comp pe ((Step.lit (F := F) (I := U) (O := S) init).typed [])
    (iterateRegion_valueBranches (t.fused.typed [])) src,
    ← exact_comp pe ((Step.lit (F := F) (I := U) (O := .sum S t.pending) (.inl init)).typed [])
    (iterateRegion_valueBranches (t.expanded.typed [])) tgt]
  change (Step.lit (F := F) (I := U) (O := S) init).arrow pe ≫ _ =
    (Step.lit (F := F) (I := U) (O := .sum S t.pending) (.inl init)).arrow pe ≫ _
  rw [← lit_left pe U S t.pending init, Category.assoc, joined_loop]

end Category

theorem fused_lowers (t : Rows F S B S) :
    (TransferPlans.source t.plans).toLetIter 1 = some (t.fused.native 0) := by
  change (S.dispatch (fun v => (t.plans v).source) (.var 0)).toLetIter 1 = _
  rw [← Rows.fused_source t]
  exact Step.lowers t.fused 0

theorem expanded_lowers (t : Rows F S B S) :
    (TransferPlans.expand t.plans).source.toLetIter 1 = some (t.expanded.native 0) :=
  Rows.expanded_source t ▸ Step.lowers t.expanded 0

section AtBound

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

/-- Exact transport for normalized tables with pure transfers. -/
theorem endpoint_transport (t : Rows F S B S) (init : S.Value)
    (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) :
    HasTypeEffect Free .nil (fusedLoop t init) B.ty e ∧
    HasTypeEffect Free .nil (expandedLoop t init) B.ty e ∧
    AbortEquiv (⊥ : ε) Free .nil (fusedLoop t init) (expandedLoop t init) B.ty ∧
    ∃ (r s : Region Ops), eraseLoop S (fusedLoop t init) = some r ∧
      eraseLoop (.sum S t.pending) (expandedLoop t init) = some s ∧
      Region.ValueBranches [Code.unit.ty] r [B.ty] ∧
      Region.ValueBranches [Code.unit.ty] s [B.ty] ∧
      Region.Paper.Extension.Eqv (Seed[(⊥ : ε)]) [Code.unit.ty] r s [B.ty] := by
  have eq : AbortEquiv (⊥ : ε) Free .nil (fusedLoop t init) (expandedLoop t init) B.ty :=
    TransferPlans.expand_eq t.plans init (nativeValue_lowers S init 0) (fused_lowers t)
      (nativeValue_lowers (.sum S t.pending) (.inl init) 0) (expanded_lowers t)
  exact ⟨typed_loop t.fused init hf he, typed_loop t.expanded (.inl init) hf he,
    eq, _, _, erase_loop t.fused init, erase_loop t.expanded (.inl init),
    loopCFG_typed _ _, loopCFG_typed _ _, joined_endpoints (⊥ : ε) t init⟩

end AtBound

section Legacy

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Mixed in
private theorem withTransfers_plans (t : Mixed.Rows F S B I) :
    t.withTransfers.plans = fun v => .ordinary (t.plans v) := by
  induction t with
  | leaf p => rfl
  | split l r il ir =>
    funext v
    cases v with
    | inl v => exact congrFun il v
    | inr v => exact congrFun ir v

theorem legacy_fused_lowers (t : Mixed.Rows F S B S) :
    (Plans.source t.plans).toLetIter 1 = some (t.fused.native 0) := by
  have lower := fused_lowers t.withTransfers
  have plans : t.withTransfers.plans = Plans.withTransfers t.plans := withTransfers_plans t
  rwa [plans, Plans.withTransfers_source] at lower

theorem legacy_expanded_lowers (t : Mixed.Rows F S B S) :
    (Plans.expand t.plans).source.toLetIter 1 = some (t.expanded.native 0) := by
  have lower := expanded_lowers t.withTransfers
  have plans : t.withTransfers.plans = Plans.withTransfers t.plans := withTransfers_plans t
  rwa [plans, Plans.withTransfers_expanded_source] at lower

/-- The missing row is well-typed even below top. The obstruction is
the normalized renderer's row grammar. -/
theorem typed_transfer_unrendered [SemilatticeSup ε] [OrderBot ε] (e : ε) (t : S.Value) :
    Wf [(S.ty, (⊥ : ε))] (.inr (S.literal t) : Expr Ops) (Code.sum B S).ty e ∧
    ∀ p : Plan F S B, p.source.toLetIter 1 ≠ (Expr.inr (S.literal t) : Expr Ops).toLetIter 1 := by
  refine ⟨.inr (literal_wf S t), fun p => ?_⟩
  rw [Expr.toLetIter, nativeValue_lowers S t 1]
  exact no_bare_transfer p 1 _

end Legacy

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Proofs.Transfer
