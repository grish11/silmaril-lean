module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Retained.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

/-! # Proofs of literal retained-context case -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CfgEta.TypeCategory
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open Paper.RetainedLet (returnOnce returnOnce_typed diagonal diagonal_typed unpackBody unpackBody_typed)
open Silmaril.DeBruijn (lift)

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B D : τ} {a : Tm Φ} {l r : Region Φ}

open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem case_arm_subst (s : Region Φ) (ρ : Nat → Nat) (value : Tm Φ) :
    ((s.renameVars (lift Nat.succ)).renameVars (lift (lift ρ))).substVars
      (Tm.liftSubst (Tm.singleSubst value)) = s.renameVars (lift ρ) := by
  rw [Region.renameVars_comp, Region.substVars_renameVars, Region.renameVars_eq_substVars]
  congr 1
  funext i
  cases i <;> rfl

private theorem choose_left {Γ : VCtx τ} {P Q : τ} {t : Tm Φ} {s s' : Region Φ}
    (ht : Tm.BranchValue Γ t P) (hs : HasType (P :: Γ) s [D]) (hs' : HasType (Q :: Γ) s' [D]) :
    Paper.Eqv Γ (.case (.inl t) s s') (s.substVars (Tm.singleSubst t)) [D] :=
  .cfgEta (.native ((SubstitutionEquiv.base (.caseInl ht.hasType hs hs')).trans (.letValue ht hs)))

private theorem choose_right {Γ : VCtx τ} {P Q : τ} {t : Tm Φ} {s s' : Region Φ}
    (ht : Tm.BranchValue Γ t Q) (hs : HasType (P :: Γ) s [D]) (hs' : HasType (Q :: Γ) s' [D]) :
    Paper.Eqv Γ (.case (.inr t) s s') (s'.substVars (Tm.singleSubst t)) [D] :=
  .cfgEta (.native ((SubstitutionEquiv.base (.caseInr ht.hasType hs hs')).trans (.letValue ht hs')))

private theorem unpack_values {Γ : VCtx τ} {u v : Tm Φ} {ρ : Nat → Nat}
    (hs : HasType [A, X] l [D])
    (hρ : Ren ([] : VCtx τ) Γ ρ) (hu : Tm.BranchValue Γ u X) (hv : Tm.BranchValue Γ v A) :
    Paper.Eqv Γ
      (((unpackBody l).renameVars (lift ρ)).substVars (Tm.singleSubst (.pair u v)))
      (l.substVars (Tm.consSubst v (Tm.consSubst u (Tm.var ∘ ρ)))) [D] := by
  let P := Silmaril.product X A
  let t := Tm.pair u v
  let ρ₀ := lift (lift Nat.succ)
  let ρ₁ := lift (lift (lift ρ))
  let σ := Tm.liftSubstN 2 (Tm.singleSubst t)
  let κ := Tm.consSubst v (Tm.singleSubst u)
  have ht : Tm.HasType Γ t P := (Tm.BranchValue.pair hu hv).hasType
  have hb : HasType (A :: X :: Γ) (((l.renameVars ρ₀).renameVars ρ₁).substVars σ) [D] :=
    ((hs.renameVars (((Ren.wk [] P).lift X).lift A)).renameVars
      (((hρ.lift P).lift X).lift A)).substVars (((Tm.Subst.HasType.single ht).lift X).lift A)
  have hβ := Paper.Eqv.productBeta (.let₂Beta hu hv hb)
  change Paper.Eqv Γ (.let₂ t (((l.renameVars ρ₀).renameVars ρ₁).substVars σ))
    ((((l.renameVars ρ₀).renameVars ρ₁).substVars σ).substVars κ) [D] at hβ
  change Paper.Eqv Γ (.let₂ t (((l.renameVars ρ₀).renameVars ρ₁).substVars σ)) _ [D]
  have eq : ((((l.renameVars ρ₀).renameVars ρ₁).substVars σ).substVars κ) =
      l.substVars (Tm.consSubst v (Tm.consSubst u (Tm.var ∘ ρ))) := by
    rw [Region.substVars_comp, Region.renameVars_comp, Region.substVars_renameVars]
    congr 1
    funext n
    cases n with
    | zero => rfl
    | succ n => cases n <;> rfl
  rw [eq] at hβ
  exact hβ

private theorem unpack_pair {Γ : VCtx τ} {i j : Nat} {ρ : Nat → Nat}
    (hs : ValueBranches [A, X] l [D])
    (hρ : Ren ([] : VCtx τ) Γ ρ) (hi : At Γ i A) (hj : At Γ j X) :
    Paper.Eqv Γ
      (((unpackBody l).renameVars (lift ρ)).substVars (Tm.singleSubst (.pair (.var j) (.var i))))
      (l.renameVars (fun | 0 => i | 1 => j | n + 2 => ρ n)) [D] := by
  rw [Region.renameVars_eq_substVars l (fun | 0 => i | 1 => j | n + 2 => ρ n)]
  have same : Tm.var (Φ := Φ) ∘ (fun | 0 => i | 1 => j | n + 2 => ρ n) =
      Tm.consSubst (.var i) (Tm.consSubst (.var j) (Tm.var ∘ ρ)) := by
    funext n
    cases n with
    | zero => rfl
    | succ n => cases n <;> rfl
  rw [same]
  exact unpack_values hs.hasType hρ (.var hj) (.var hi)

private theorem packed_arms_branch {ρ : Nat → Nat} (term : Tm Φ) :
    ((packedArms l r).renameVars (lift ρ)).substVars (Tm.singleSubst term) =
      .case term ((unpackBody l).renameVars (lift ρ)) ((unpackBody r).renameVars (lift ρ)) := by
  simp only [packedArms, boundCase, Region.renameVars, Region.substVars, Tm.rename, Tm.subst,
    case_arm_subst]
  rfl

theorem route_normalizes (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.Eqv [Silmaril.product X (Silmaril.coprod A B)]
      (routeCase l r) (unpackBody (boundCase l r)) [D] := by
  let S := Silmaril.coprod A B
  let T := Silmaril.product X S
  let P := Silmaril.product X A
  let Q := Silmaril.product X B
  let ρ := Nat.succ ∘ Nat.succ ∘ Nat.succ ∘ Nat.succ
  let ρ' : Nat → Nat := fun | 0 => 0 | 1 => 2 | n + 2 => ρ n
  have left : Paper.Eqv [A, S, X, T]
      (((packedArms l r).renameVars (lift ρ)).substVars
        (Tm.singleSubst (.inl (.pair (.var 2) (.var 0)))))
      (l.renameVars ρ') [D] := by
    have w : Ren ([] : VCtx τ) [A, S, X, T] ρ := by
      intro i C h
      simp [At] at h
    rw [packed_arms_branch]
    have h : Tm.BranchValue [A, S, X, T] (.pair (.var 2) (.var 0) : Tm Φ) P :=
      .pair (.var (i := 2) rfl) (.var (i := 0) rfl)
    have choose := choose_left h ((unpackBody_typed hl).hasType.renameVars (w.lift P))
      ((unpackBody_typed hr).hasType.renameVars (w.lift Q))
    exact choose.trans (unpack_pair hl w (i := 0) (j := 2) rfl rfl)
  have right : Paper.Eqv [B, S, X, T]
      (((packedArms l r).renameVars (lift ρ)).substVars
        (Tm.singleSubst (.inr (.pair (.var 2) (.var 0)))))
      (r.renameVars ρ') [D] := by
    have w : Ren ([] : VCtx τ) [B, S, X, T] ρ := by
      intro i C h
      simp [At] at h
    rw [packed_arms_branch]
    have h : Tm.BranchValue [B, S, X, T] (.pair (.var 2) (.var 0) : Tm Φ) Q :=
      .pair (.var (i := 2) rfl) (.var (i := 0) rfl)
    have choose := choose_right h ((unpackBody_typed hl).hasType.renameVars (w.lift P))
      ((unpackBody_typed hr).hasType.renameVars (w.lift Q))
    exact choose.trans (unpack_pair hr w (i := 0) (j := 2) rfl rfl)
  have eqLeft : routeCase l r =
      .let₂ (.var 0) (.case (.var 0)
        (((packedArms l r).renameVars (lift ρ)).substVars (Tm.singleSubst (.inl (.pair (.var 2) (.var 0)))))
        (((packedArms l r).renameVars (lift ρ)).substVars (Tm.singleSubst (.inr (.pair (.var 2) (.var 0)))))) := by
    simp only [routeCase, compLSubst, distributorRegion, lsubst, liftLSubstVars, Region.renameVars_comp]
    congr 5 <;> funext i <;> cases i <;> rfl
  have eqRight : unpackBody (boundCase l r) =
      .let₂ (.var 0) (.case (.var 0) (l.renameVars ρ') (r.renameVars ρ')) := by
    simp only [unpackBody, boundCase, Region.renameVars, Tm.rename, Region.renameVars_comp]
    congr 5 <;> funext i <;> cases i with
      | zero => rfl
      | succ i => cases i <;> rfl
  rw [eqLeft, eqRight]
  exact .let₂ (.var (i := 0) rfl) (.case (.var (i := 0) rfl) left right)

theorem single_bind_case (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.Eqv [X] (assembleCase (returnOnce a) l r) (.let₁ a (boundCase l r)) [D] := by
  let T := Silmaril.product X (Silmaril.coprod A B)
  have hp : ValueBranches [X] _ [T] :=
    seqValueBranches (diagonal_typed (Φ := Φ) X) (whiskerLeftRegion_typed X (returnOnce_typed ha))
  have h := (route_normalizes hl hr).renameVars ((Ren.wk ([] : VCtx τ) X).lift T)
  have e := Paper.lsubst_singleton_congr hp h
  change Paper.Eqv [X]
    (compLSubst (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion (returnOnce a))) (fun _ => routeCase l r) 0)
    _ [D] at e
  unfold assembleCase
  rw [compLSubst_assoc]
  exact e.trans (Paper.RetainedLet.literal_let ha (boundCase_typed hl hr).hasType)

private def returnSumWithInput (a : Tm Φ) : Region Φ :=
  .case a (.br 0 (.pair (.var 1) (.inl (.var 0)))) (.br 0 (.pair (.var 1) (.inr (.var 0))))

private theorem returnSumWithInput_typed (ha : Tm.HasType [X] a (Silmaril.coprod A B)) :
    ValueBranches [X] (returnSumWithInput a) [Silmaril.product X (Silmaril.coprod A B)] :=
  .case ha
    (.br rfl (.pair (.var (i := 1) rfl) (.inl (.var (i := 0) rfl))))
    (.br rfl (.pair (.var (i := 1) rfl) (.inr (.var (i := 0) rfl))))

private theorem duplicate_whisker_returnSum (ha : Tm.HasType [X] a (Silmaril.coprod A B)) :
    Paper.Eqv [X] (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion (returnSum a)) 0)
      (returnSumWithInput a) [Silmaril.product X (Silmaril.coprod A B)] := by
  let P := Silmaril.product X X
  let t := Tm.pair (.var 0) (.var 0) (Φ := Φ)
  let σ := Tm.liftSubstN 2 (Tm.singleSubst t)
  let κ := Tm.consSubst (.var 0) (Tm.singleSubst (.var 0 : Tm Φ))
  let b := whiskerLeftBody (returnSum a)
  let υ := lift (lift (lift Nat.succ))
  have ht : Tm.HasType [X] t P := .pair (.var (i := 0) rfl) (.var (i := 0) rfl)
  have hb : Region.HasType [X, X, X] ((b.renameVars υ).substVars σ) [Silmaril.product X (Silmaril.coprod A B)] :=
    ((whiskerLeftBody_typed X (returnSum_typed ha)).hasType.renameVars
      ((((Ren.wk [] X).lift P).lift X).lift X)).substVars
      (((Tm.Subst.HasType.single ht).lift X).lift X)
  have hβ := Paper.Eqv.productBeta (.let₂Beta (.var (i := 0) (rfl : At [X] 0 X))
    (.var (i := 0) (rfl : At [X] 0 X)) hb)
  change Paper.Eqv [X] (.let₂ t ((b.renameVars υ).substVars σ))
    (((b.renameVars υ).substVars σ).substVars κ) [Silmaril.product X (Silmaril.coprod A B)] at hβ
  have eqA : ((((a.rename (lift (Nat.succ ∘ Nat.succ))).rename υ).subst σ).subst κ) = a := by
    rw [Tm.rename_comp, Tm.subst_comp, Tm.subst_rename]
    refine (Paper.RetainedLet.term_subst_eq ha (η := Tm.var) ?_).trans (Tm.subst_var a)
    intro i C hi
    cases i with
    | zero => rfl
    | succ i => simp [At] at hi
  change Paper.Eqv [X] _ (returnSumWithInput a) [Silmaril.product X (Silmaril.coprod A B)]
  have eq : ((b.renameVars υ).substVars σ).substVars κ = returnSumWithInput a := by
    change Region.case ((((a.rename (lift (Nat.succ ∘ Nat.succ))).rename υ).subst σ).subst κ)
      (.br 0 (.pair (.var 1) (.inl (.var 0)))) (.br 0 (.pair (.var 1) (.inr (.var 0)))) = _
    rw [eqA]
    rfl
  rw [eq] at hβ
  exact hβ

private theorem drop_payload (s : Region Φ) :
    (s.renameVars (lift Nat.succ)).substVars (Tm.singleSubst (.var 0)) = s :=
  congrFun (compLSubst_id_left (fun _ => s)) 0

private theorem boundCase_subst_tag (t : Tm Φ) :
    (boundCase l r).substVars (Tm.replaceNewest t) =
      .case t (l.renameVars (lift Nat.succ)) (r.renameVars (lift Nat.succ)) := by
  have same : Tm.liftSubst (Tm.replaceNewest t) ∘ lift Nat.succ =
      Tm.var ∘ lift Nat.succ := by
    funext i
    cases i <;> rfl
  simp only [boundCase, substVars, Tm.subst, Region.substVars_renameVars, same,
    ← Region.renameVars_eq_substVars]
  rfl

private theorem returnSumWithInput_unpack (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.Eqv [X] (compLSubst (fun _ => returnSumWithInput a) (fun _ => unpackBody (boundCase l r)) 0)
      (.case a l r) [D] := by
  let ρ := Nat.succ ∘ Nat.succ
  have same (t : Tm Φ) :
      Tm.consSubst t (Tm.consSubst (.var 1) (Tm.var ∘ ρ)) = Tm.replaceNewest t := by
    funext i
    cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  have hleft : Paper.Eqv [A, X]
      (((unpackBody (boundCase l r)).renameVars (lift ρ)).substVars
        (Tm.singleSubst (.pair (.var 1) (.inl (.var 0))))) l [D] := by
    have w : Ren ([] : VCtx τ) [A, X] ρ := by
      intro i C h
      simp [At] at h
    have h := unpack_values (boundCase_typed hl hr).hasType w
      (.var (i := 1) (rfl : At [A, X] 1 X)) (.inl (B := B) (.var (i := 0) rfl))
    rw [same, boundCase_subst_tag] at h
    have k := choose_left (.var (i := 0) (rfl : At [A, X] 0 A))
      (hl.hasType.renameVars ((Ren.wk [X] A).lift A))
      (hr.hasType.renameVars ((Ren.wk [X] A).lift B))
    rw [drop_payload] at k
    exact h.trans k
  have hright : Paper.Eqv [B, X]
      (((unpackBody (boundCase l r)).renameVars (lift ρ)).substVars
        (Tm.singleSubst (.pair (.var 1) (.inr (.var 0))))) r [D] := by
    have w : Ren ([] : VCtx τ) [B, X] ρ := by
      intro i C h
      simp [At] at h
    have h := unpack_values (boundCase_typed hl hr).hasType w
      (.var (i := 1) (rfl : At [B, X] 1 X)) (.inr (A := A) (.var (i := 0) rfl))
    rw [same, boundCase_subst_tag] at h
    have k := choose_right (.var (i := 0) (rfl : At [B, X] 0 B))
      (hl.hasType.renameVars ((Ren.wk [X] B).lift A))
      (hr.hasType.renameVars ((Ren.wk [X] B).lift B))
    rw [drop_payload] at k
    exact h.trans k
  have eq : compLSubst (fun _ => returnSumWithInput a) (fun _ => unpackBody (boundCase l r)) 0 =
      .case a
        (((unpackBody (boundCase l r)).renameVars (lift ρ)).substVars
          (Tm.singleSubst (.pair (.var 1) (.inl (.var 0)))))
        (((unpackBody (boundCase l r)).renameVars (lift ρ)).substVars
          (Tm.singleSubst (.pair (.var 1) (.inr (.var 0))))) := by
    simp only [compLSubst, returnSumWithInput, lsubst, liftLSubstVars, Region.renameVars_comp]
    congr 4 <;> funext i <;> cases i <;> rfl
  rw [eq]
  exact .case ha hleft hright

theorem literal_case (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.Eqv [X] (assembleCase (returnSum a) l r) (.case a l r) [D] := by
  let T := Silmaril.product X (Silmaril.coprod A B)
  have hp : ValueBranches [X] _ [T] :=
    seqValueBranches (diagonal_typed (Φ := Φ) X) (whiskerLeftRegion_typed X (returnSum_typed ha))
  have hq := returnSumWithInput_typed ha
  have h := (route_normalizes hl hr).renameVars ((Ren.wk ([] : VCtx τ) X).lift T)
  have e := Paper.lsubst_singleton_congr hp h
  change Paper.Eqv [X]
    (compLSubst (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion (returnSum a))) (fun _ => routeCase l r) 0)
    _ [D] at e
  have hPost := (duplicate_whisker_returnSum ha).lsubstPost hp hq
    (fun _ _ hi => (((singletonValueFamily (unpackBody_typed (boundCase_typed hl hr))).liftVars X) hi).hasType)
  unfold assembleCase
  rw [compLSubst_assoc]
  exact e.trans (hPost.trans (returnSumWithInput_unpack ha hl hr))

section Semantics

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (denote_weakenCapture)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_bind_value)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext)

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
/-- The semantic case-bind law moves a scrutinee bind into the case without
any premise on the scrutinee or the regions in its arms. -/
theorem denote_boundCase_let {Γ : VCtx τ} {L : LCtx τ} (ha : Tm.HasType Γ a (Silmaril.coprod A B))
    (hl : HasType (A :: Γ) l L) (hr : HasType (B :: Γ) r L) :
    denoteRegion J M (.let₁ ha (boundCase_hasType hl hr)) = denoteRegion J M (.case ha hl hr) := by
  let S := Silmaril.coprod A B
  have hs := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (S :: Γ) 0 S)
  have hd := denote_spec J M ha
  have hlw := hl.renameVars ((Ren.wk Γ S).lift A)
  have hrw := hr.renameVars ((Ren.wk Γ S).lift B)
  have hc := RegionDenotes.case hs (denoteRegion_spec J M hlw) (denoteRegion_spec J M hrw)
  rw [← (RegionDenotes.let₁ hd hc).eq_denote J M,
    ← (RegionDenotes.case hd (denoteRegion_spec J M hl) (denoteRegion_spec J M hr)).eq_denote J M,
    denote_weakenCapture M J (B := S) hl, denote_weakenCapture M J (B := S) hr, ← J.map_comp]
  change _ = caseWithContext J (denote J M ha ≫ J.map (M.coprodIso A B).hom)
    (denoteRegion J M hl) (denoteRegion J M hr)
  exact (case_bind_value J (denote J M ha) (M.coprodIso A B).hom
    (denoteRegion J M hl) (denoteRegion J M hr)).symm

variable [FreydCategory.CentralUnit J]

set_option backward.isDefEq.respectTransparency false in
/-- Case and immediate retagging preserve the arbitrary scrutinee's
denotation, including its effects. -/
theorem returnSum_denotation (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    {f : J.obj (ctxObj M [X]) ⟶ J.obj (M.obj (Silmaril.coprod A B))}
    (d : Denotes J M ha f) :
    denoteSingletonRegion J M (returnSum_typed ha).hasType =
      J.map ((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ f := by
  let S := Silmaril.coprod A B
  let E := ctxObj M [X]
  let tag := labelInject M 0 (rfl : At [S] 0 S)
  let p := (M.coprodIso A B)
  let left := (coprod.inl : M.obj A ⟶ M.obj A ⨿ M.obj B) ≫ p.inv ≫ tag
  let right := (coprod.inr : M.obj B ⟶ M.obj A ⨿ M.obj B) ≫ p.inv ≫ tag
  have lookupLeft : lookup M 0 (rfl : At [A, X] 0 A) =
      CartesianMonoidalCategory.snd E (M.obj A) := by simp [lookup]; rfl
  have lookupRight : lookup M 0 (rfl : At [B, X] 0 B) =
      CartesianMonoidalCategory.snd E (M.obj B) := by simp [lookup]; rfl
  have leftDenotes : RegionDenotes J M (Φ := Φ)
      (.br (rfl : At [S] 0 S) (.inl (B := B) (.var (i := 0) (rfl : At [A, X] 0 A))))
      (J.map (CartesianMonoidalCategory.snd E (M.obj A) ≫ left)) := by
    simpa only [left, p, tag, lookupLeft, Category.assoc, J.map_comp] using
      (RegionDenotes.br (h := (rfl : At [S] 0 S))
        (Denotes.inl (B := B) (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [A, X] 0 A))))
  have rightDenotes : RegionDenotes J M (Φ := Φ)
      (.br (rfl : At [S] 0 S) (.inr (A := A) (.var (i := 0) (rfl : At [B, X] 0 B))))
      (J.map (CartesianMonoidalCategory.snd E (M.obj B) ≫ right)) := by
    simpa only [right, p, tag, lookupRight, Category.assoc, J.map_comp] using
      (RegionDenotes.br (h := (rfl : At [S] 0 S))
        (Denotes.inr (A := A) (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [B, X] 0 B))))
  have equation := (RegionDenotes.case d leftDenotes rightDenotes).eq_denote J M
  change _ = denoteRegion J M (returnSum_typed ha).hasType at equation
  rw [Silmaril.Isotope.LetIter.Semantics.Categorical.case_return_map J] at equation
  have collected : coprod.desc left right = p.inv ≫ tag := by
    apply coprod.hom_ext
    · simp [left]
    · simp [right]
  rw [collected, Category.assoc, ← J.map_comp, Iso.hom_inv_id_assoc] at equation
  have eq : denoteRegion J M (returnSum_typed ha).hasType =
      denoteRegion J M (.br (rfl : At [S] 0 S) ha) :=
    equation.symm.trans ((RegionDenotes.br (h := (rfl : At [S] 0 S)) d).eq_denote J M)
  have result := denoteSingletonRegion_br J M d
  unfold denoteSingletonRegion at result ⊢
  rw [eq]
  exact result

/-- The full assembled case for the single-bind representative has the
denotation of the literal case on the original arbitrary scrutinee. -/
theorem denote_single_bind_case
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    denoteRegion J M (assembleCase_typed (returnOnce_typed ha) hl hr).hasType =
      denoteRegion J M (.case ha hl.hasType hr.hasType) :=
  (Paper.Eqv.sound J M shared (single_bind_case ha hl hr) (assembleCase_typed (returnOnce_typed ha) hl hr).hasType
    (.let₁ ha (boundCase_hasType hl.hasType hr.hasType))).trans
    (denote_boundCase_let J M ha hl.hasType hr.hasType)

end Semantics

section Quotient

open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
theorem assembleCase_ofRegion {p : Region Φ} (hp : ValueBranches [X] p [Silmaril.coprod A B])
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    assembledCaseArrow hp hl hr = Paper.TypeCategory.ofRegion (assembleCase_typed hp hl hr) := by
  unfold assembledCaseArrow
  dsimp only
  rw [Paper.TypeCategory.whiskerLeft_ofRegion]
  rw [Paper.TypeCategory.ofRegion_comp _ _
      (seqValueBranches (diagonal_typed X) (whiskerLeftRegion_typed X hp)),
    Paper.TypeCategory.ofRegion_comp _ _
      (seqValueBranches
        (seqValueBranches (diagonal_typed X) (whiskerLeftRegion_typed X hp))
        (distributorRegion_typed X A B)),
    Paper.TypeCategory.ofRegion_comp _ _ (assembleCase_typed hp hl hr)]

theorem single_bind_case_ofRegion (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    assembledCaseArrow (returnOnce_typed ha) hl hr = Paper.TypeCategory.ofRegion (.let₁ ha (boundCase_typed hl hr)) :=
  (assembleCase_ofRegion (returnOnce_typed ha) hl hr).trans
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).2 (single_bind_case ha hl hr))

theorem literal_case_ofRegion (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    assembledCaseArrow (returnSum_typed ha) hl hr = Paper.TypeCategory.ofRegion (.case ha hl hr) :=
  (assembleCase_ofRegion (returnSum_typed ha) hl hr).trans
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).2 (literal_case ha hl hr))

theorem single_bind_case_eq_literal_iff (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    assembledCaseArrow (returnOnce_typed ha) hl hr = Paper.TypeCategory.ofRegion (.case ha hl hr) ↔
      Paper.Eqv [X] (.let₁ a (boundCase l r)) (.case a l r) [D] := by
  rw [single_bind_case_ofRegion ha hl hr]
  exact Paper.TypeCategory.ofRegion_eq_iff _ _

theorem single_bind_case_ofRegion_value (ha : Tm.BranchValue [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    assembledCaseArrow (returnOnce_typed ha.hasType) hl hr = Paper.TypeCategory.ofRegion (.case ha.hasType hl hr) := by
  apply (single_bind_case_eq_literal_iff ha.hasType hl hr).2
  have drop : Tm.liftSubst (Tm.singleSubst a) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  simpa only [boundCase, substVars, Tm.subst, Tm.singleSubst, Tm.consSubst, Region.substVars_renameVars, drop, substVars_var]
    using Paper.Eqv.cfgEta (.native (.letValue ha (boundCase_hasType hl.hasType hr.hasType)))

theorem routeCase_ofRegion (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.TypeCategory.ofRegion (τ := τ) (distributorRegion_typed X A B) ≫
      Paper.TypeCategory.ofRegion (τ := τ) (packedArms_typed hl hr) =
        Paper.TypeCategory.ofRegion (unpackBody_typed (boundCase_typed hl hr)) := by
  rw [Paper.TypeCategory.ofRegion_comp _ _ (routeCase_typed hl hr)]
  exact (Paper.TypeCategory.ofRegion_eq_iff _ _).2 (route_normalizes hl hr)

end Quotient

section Transport

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext extend)
open CfgEta.TypeCategory.Retained (packedDistributor packedCopair case_factor)

universe u₁ v₁

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ Paper.TypeCategory (τ := τ) Φ) (M : TypeModel τ V)
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ Paper.TypeCategory.ofType (Φ := Φ) T)
  {Y Z : τ}

private theorem reindex_comp {W : τ} (f : J.obj (M.obj Y) ⟶ J.obj (M.obj Z))
    (g : J.obj (M.obj Z) ⟶ J.obj (M.obj W)) :
    reindexHom J M objIso (f ≫ g) = reindexHom J M objIso f ≫ reindexHom J M objIso g := by
  simp [reindexHom]

variable [SymmetricCategory V]
  [PremonoidalCategory (Paper.TypeCategory (τ := τ) Φ)]
  [SymmetricPremonoidalCategory (Paper.TypeCategory (τ := τ) Φ)]
  [HasFiniteCoproducts (Paper.TypeCategory (τ := τ) Φ)]
  [DistributiveTensor V] [DistributivePremonoidalCategory (Paper.TypeCategory (τ := τ) Φ)]
  [DistributiveFreydCategory J]

set_option backward.isDefEq.respectTransparency false in
/-- The literal case comparison in a Paper quotient model reduces to the
retained scrutinee, the packed arms and the explicit distributor square. -/
theorem literal_case_transport
    (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D])
    (f : J.obj (M.obj X) ⟶ J.obj (M.obj (Silmaril.coprod A B)))
    (g : J.obj (M.obj (Silmaril.product X A)) ⟶ J.obj (M.obj D))
    (h : J.obj (M.obj (Silmaril.product X B)) ⟶ J.obj (M.obj D))
    (hRetained : reindexHom J M objIso
      (extend J f ≫ J.map (M.productIso X (Silmaril.coprod A B)).inv) =
      Paper.TypeCategory.ofRegion (τ := τ) (diagonal_typed X) ≫
        Paper.TypeCategory.whiskerLeft (τ := τ) (Paper.TypeCategory.ofType (Φ := Φ) X)
          (Paper.TypeCategory.ofRegion (τ := τ) (returnSum_typed ha)))
    (hDistributor : reindexHom J M objIso (J.map (packedDistributor M X A B)) =
      Paper.TypeCategory.ofRegion (τ := τ) (distributorRegion_typed X A B))
    (hArms : reindexHom J M objIso (packedCopair J M g h) =
      Paper.TypeCategory.ofRegion (τ := τ) (packedArms_typed hl hr)) :
    reindexHom J M objIso (caseWithContext J (f ≫ J.map (M.coprodIso A B).hom)
      (J.map (M.productIso X A).inv ≫ g) (J.map (M.productIso X B).inv ≫ h)) =
        Paper.TypeCategory.ofRegion (.case ha hl hr) := by
  rw [case_factor M J f g h, ← Category.assoc, reindex_comp, reindex_comp, hRetained, hDistributor, hArms]
  exact literal_case_ofRegion ha hl hr

end Transport

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase
