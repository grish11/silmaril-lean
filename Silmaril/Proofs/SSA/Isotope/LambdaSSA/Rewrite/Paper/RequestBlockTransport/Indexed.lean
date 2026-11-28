module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Indexed.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlockTransport
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Proofs.Indexed

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Indexed
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {I J O P S B : Code}

local notation "Ops" => Opcode F
local notation "U" => Code.unit

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns (requestBlocks iterateChosen_requestBlocks)
open Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory (iterateRegion_valueBranches)
open Silmaril.Isotope.LetIter.LocallyNameless (HasTypeEffect AbortEquiv)

set_option backward.isDefEq.respectTransparency false

variable {ε : Type} [HasEff (Opcode F) ε]

set_option hygiene false in
local notation "Seed[" p "]" => targetSeed (F := F) (ε := ε) p

theorem Rows.firstMap_mapOut (t : Rows F S B I) (g : t.pending.Value → O.Value)
    (f : O.Value → P.Value) :
    Step.mapOut f (t.firstMap g) = t.firstMap (fun v => f (g v)) := by
  induction t with
  | leaf req x k =>
    simp [Rows.firstMap, Step.mapOut, literal_map]
    rfl
  | split l r il ir => simp [Rows.firstMap, Step.mapOut, il, ir]

theorem Rows.fused_source (t : Rows F S B I) :
    t.fused.source = I.dispatch (fun v => (t.plans v).source) (.var 0) := by
  induction t with
  | leaf f x k =>
    simp [Rows.fused, Rows.plans, Step.source, tabulate_source, row_source, Code.dispatch, Plan.source]
  | split l r il ir =>
    simp [Rows.fused, Step.source, Code.dispatch, Rows.plans, il, ir]

private def firstSource (fallback : Row F S B → Expr Ops) :
    (p : Plan F S B) → (p.replyCode.Value → P.Value) → Expr Ops
  | .one r, _ => fallback r
  | .two f x _, tag => .let₁ (.op f (f.argCode.literal x))
      (f.replyCode.dispatch (fun r => P.literal (tag r)) (.var 0))

private theorem Rows.firstMap_source (t : Rows F S B I) (tag : t.pending.Value → P.Value)
    (fallback : Row F S B → Expr Ops) :
    (t.firstMap tag).source =
      I.dispatch (fun v => firstSource fallback (t.plans v)
        (fun r => tag (Code.encode I (fun s => (t.plans s).replyCode) v r))) (.var 0) := by
  induction t with
  | leaf f x k =>
    simp [Rows.firstMap, Rows.plans, Step.source, literals, tabulate_source, Code.dispatch, Code.encode, firstSource]
  | split l r il ir =>
    simp [Rows.firstMap, Step.source, Code.dispatch, Rows.plans, Code.encode, il, ir]

theorem Rows.second_map_source (t : Rows F S B I) (inject : S.Value → J.Value) :
    (Step.mapOut (O := .sum B S) (P := .sum B J) (Sum.map id inject) t.second).source =
      t.pending.dispatch (fun w =>
        let p := Code.decode I (fun v => (t.plans v).replyCode) w
        (((t.plans p.1).second p.2).map inject).source) (.var 0) := by
  induction t with
  | leaf f x k =>
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

private theorem firstSource_expanded (p : Plan F S B) (encode : p.replyCode.Value → J.Value) :
    firstSource (fun r => (r.map (T := .sum S J) Sum.inl).source) (P := .sum B (.sum S J))
      p (fun v => .inr (.inr (encode v))) = (p.expandFirst J encode).source := by
  cases p <;> rfl

theorem Rows.expanded_source (t : Rows F S B S) :
    t.expanded.source = (Plans.expand (t.plans : Plans F S B)).source := by
  rw [Rows.expanded, Step.source, Rows.firstMap_source _ _ (fun r => (r.map (T := .sum S t.pending) Sum.inl).source),
    Rows.second_map_source (J := .sum S t.pending) t Sum.inl, Heterogeneous.Table.source, Code.dispatch]
  congr 1
  · apply congrArg (fun rows => S.dispatch rows (.var 0))
    funext v
    exact firstSource_expanded (t.plans v) (Code.encode S (fun s => (t.plans s).replyCode) v)

section Category

variable (pe : ε)
set_option hygiene false in
local notation "Obj" => ofType (Seed[pe])

private theorem split_left (l : Step F I O) (r : Step F J O) :
    left pe I J ≫ (Step.split l r).arrow pe = l.arrow pe := by
  rw [← left_inv, Category.assoc, split_arrow, coprod.inl_desc]

private theorem split_right (l : Step F I O) (r : Step F J O) :
    right pe I J ≫ (Step.split l r).arrow pe = r.arrow pe := by
  rw [← right_inv, Category.assoc, split_arrow, coprod.inr_desc]

private theorem first_tag (t : Rows F S B I) (tag : t.pending.Value → P.Value)
    (g : Obj t.pending.ty ⟶ Obj P.ty)
    (leaf : ∀ (C : Code) x, (Step.lit (I := C) (O := t.pending) x : Step F C t.pending).arrow pe ≫ g =
      (Step.lit (I := C) (O := P) (tag x) : Step F C P).arrow pe) :
    (t.firstMap tag).arrow pe = t.first.arrow pe ≫ g := by
  have tr := mapOut_arrow pe t.first tag g leaf
  rw [Rows.first, Rows.firstMap_mapOut] at tr
  exact tr

/-- The dependent pending code is the middle object of the original
table's first-request/second-row factorization. -/
theorem factor (t : Rows F S B I) :
    t.first.arrow pe ≫ t.second.arrow pe = t.fused.arrow pe := by
  induction t with
  | leaf f x k =>
    rw [Rows.first, Rows.firstMap, call_arrow, literals_id, Category.comp_id,
      Rows.fused, call_arrow, Rows.second]
  | @split L R l r il ir =>
    apply (cancel_epi (sumIso (Seed[pe]) L.ty R.ty).inv).mp
    rw [Rows.fused, split_arrow, ← Category.assoc, Rows.first, Rows.firstMap, split_arrow]
    apply coprod.hom_ext
    · simp only [coprod.inl_desc_assoc, coprod.inl_desc]
      change (l.firstMap (P := .sum l.pending r.pending) Sum.inl).arrow pe ≫
        (Step.split l.second r.second).arrow pe = _
      rw [first_tag pe l (P := .sum l.pending r.pending) Sum.inl (left pe l.pending r.pending)
        (fun C x => lit_left pe C l.pending r.pending x), Category.assoc, split_left, il]
    · simp only [coprod.inr_desc_assoc, coprod.inr_desc]
      change (r.firstMap (P := .sum l.pending r.pending) Sum.inr).arrow pe ≫
        (Step.split l.second r.second).arrow pe = _
      rw [first_tag pe r (P := .sum l.pending r.pending) Sum.inr (right pe l.pending r.pending)
        (fun C x => lit_right pe C l.pending r.pending x), Category.assoc, split_right, ir]

private theorem first_pending (t : Rows F S B S) :
    (t.firstMap (P := .sum B (.sum S t.pending)) (fun v => .inr (.inr v))).arrow pe =
      t.first.arrow pe ≫ right pe S t.pending ≫ right pe B (.sum S t.pending) :=
  first_tag pe t _ _ (fun C v => by rw [← Category.assoc, lit_right, lit_right])

private theorem expanded_coords (t : Rows F S B S) :
    (sumIso (Seed[pe]) S.ty t.pending.ty).inv ≫ t.expanded.arrow pe ≫
        (sumIso (Seed[pe]) B.ty (.sum S t.pending : Code).ty).hom =
      requestBlocks pe (t.first.arrow pe)
        (t.second.arrow pe ≫ (sumIso (Seed[pe]) B.ty S.ty).hom) ≫
          (coprod.associator (Obj B.ty) (Obj S.ty) (Obj t.pending.ty)).hom ≫
            coprod.map (𝟙 (Obj B.ty)) (sumIso (Seed[pe]) S.ty t.pending.ty).inv := by
  rw [← Category.assoc, Rows.expanded, split_arrow, coprod.desc_comp]
  apply coprod.hom_ext
  · simp only [coprod.inl_desc, requestBlocks, Category.assoc, coprod.inl_desc_assoc]
    simp only [first_pending, Category.assoc, right_coord]
    simp [coprod.associator, Category.assoc]
    change _ = t.first.arrow pe ≫
      (coprod.inr : Obj t.pending.ty ⟶ Obj S.ty ⨿ Obj t.pending.ty) ≫
        (sumIso (Seed[pe]) S.ty t.pending.ty).inv ≫ coprod.inr
    rw [← Category.assoc (coprod.inr : Obj t.pending.ty ⟶ Obj S.ty ⨿ Obj t.pending.ty), right_inv]
    rfl
  · simp only [coprod.inr_desc, requestBlocks, Category.assoc, coprod.inr_desc_assoc]
    rw [lift_control]
    congr 2
    apply coprod.hom_ext
    · simp [coprod.associator]
      rfl
    · simp [coprod.associator, Category.assoc]
      change _ = (coprod.inl : Obj S.ty ⟶ Obj S.ty ⨿ Obj t.pending.ty) ≫
        (sumIso (Seed[pe]) S.ty t.pending.ty).inv ≫ coprod.inr
      rw [← Category.assoc, left_inv]
      rfl

private theorem joined_loop (t : Rows F S B S) :
    ofRegion (Seed[pe]) (iterateRegion_valueBranches (t.fused.typed [])) =
      left pe S t.pending ≫ ofRegion (Seed[pe]) (iterateRegion_valueBranches (t.expanded.typed [])) := by
  rw [← loop_coords, ← loop_coords, ← factor pe t, Category.assoc, iterateChosen_requestBlocks]
  let compare := sumIso (Seed[pe]) S.ty t.pending.ty
  have eq := uniformity_of_iso (Seed[pe]) compare.symm
    (requestBlocks pe (t.first.arrow pe) (t.second.arrow pe ≫ (sumIso (Seed[pe]) B.ty S.ty).hom) ≫
      (coprod.associator (Obj B.ty) (Obj S.ty) (Obj t.pending.ty)).hom)
    (t.expanded.arrow pe ≫ (sumIso (Seed[pe]) B.ty (.sum S t.pending : Code).ty).hom)
    (by
      change (_ ≫ _) ≫ coprod.map (𝟙 (Obj B.ty)) compare.inv = compare.inv ≫ _ ≫ _
      rw [Category.assoc]
      exact (expanded_coords pe t).symm)
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
    (Plans.source t.plans).toLetIter 1 = some (t.fused.native 0) := by
  change (S.dispatch (fun v => (t.plans v).source) (.var 0)).toLetIter 1 = _
  rw [← Rows.fused_source t]
  exact Step.lowers t.fused 0

theorem expanded_lowers (t : Rows F S B S) :
    (Plans.expand t.plans).source.toLetIter 1 = some (t.expanded.native 0) :=
  Rows.expanded_source t ▸ Step.lowers t.expanded 0

section AtBound

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

/-- Both endpoints are the #3846 lowerings at the same supplied bound.
The joined equality comes from the factorization through the indexed
pending-reply code and the request-block iteration law. -/
theorem endpoint_transport (t : Rows F S B S) (init : S.Value)
    (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) :
    HasTypeEffect Free .nil (RequestBlockTransport.Indexed.fusedNative t init) B.ty e ∧
    HasTypeEffect Free .nil (RequestBlockTransport.Indexed.expandedNative t init) B.ty e ∧
    AbortEquiv (⊥ : ε) Free .nil
      (RequestBlockTransport.Indexed.fusedNative t init) (RequestBlockTransport.Indexed.expandedNative t init) B.ty ∧
    ∃ (r s : Region Ops), eraseLoop S (RequestBlockTransport.Indexed.fusedNative t init) = some r ∧
      eraseLoop (.sum S t.pending) (RequestBlockTransport.Indexed.expandedNative t init) = some s ∧
      Region.ValueBranches [Code.unit.ty] r [B.ty] ∧
      Region.ValueBranches [Code.unit.ty] s [B.ty] ∧
      Region.Paper.Extension.Eqv (Seed[(⊥ : ε)]) [Code.unit.ty] r s [B.ty] := by
  have eq : AbortEquiv (⊥ : ε) Free .nil
      (RequestBlockTransport.Indexed.fusedNative t init) (RequestBlockTransport.Indexed.expandedNative t init) B.ty :=
    Plans.expand_eq t.plans init (nativeValue_lowers S init 0) (fused_lowers t)
      (nativeValue_lowers (.sum S t.pending) (.inl init) 0) (expanded_lowers t)
  exact ⟨typed_loop t.fused init hf he, typed_loop t.expanded (.inl init) hf he,
    eq, _, _, erase_loop t.fused init, erase_loop t.expanded (.inl init),
    loopCFG_typed _ _, loopCFG_typed _ _, joined_endpoints (⊥ : ε) t init⟩

end AtBound

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Proofs.Indexed
