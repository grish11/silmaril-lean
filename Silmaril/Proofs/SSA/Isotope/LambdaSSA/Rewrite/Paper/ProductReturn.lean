module
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Copy.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms

/-! # Return witnesses for sequential singleton pairing -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductReturn

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory
open CfgEta.TypeCategory (seqValueBranches whiskerRightRegion whiskerRightBody whiskerRightBody_typed
  whiskerLeftRegion whiskerLeftBody whiskerLeftBody_typed whiskerRightRegion_typed whiskerLeftRegion_typed
  returnRegion returnRegion_typed returnRegion_rename returnRegion_branchValue)
open Silmaril.DeBruijn (lift)
open CategoryTheory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private abbrev seq (r s : Region Φ) := compLSubst (fun _ => r) (fun _ => s) 0
private abbrev retain : Region Φ := .br 0 (.pair (.var 0) (.var 1))
private abbrev finish : Region Φ := .br 0 (.pair (.var 1) (.var 0))

private abbrev replaceZero (a : Tm Φ) := Tm.consSubst a (Tm.var ∘ Nat.succ)

private theorem send_then (a : Tm Φ) (r : Region Φ) :
    seq (.br 0 a) r = r.substVars (replaceZero a) := by
  simp only [compLSubst, lsubst, liftLSubstVars, substVars_renameVars]
  congr 1
  funext i
  cases i <;> rfl

private theorem rightOnDiagonal {X A : τ} {r : Region Φ} (hr : ValueBranches [X] r [A]) :
    Paper.Eqv [X] (seq (Paper.RetainedLet.diagonal : Region Φ) (whiskerRightRegion r))
      (r.lsubst (fun _ => retain)) [product A X] := by
  let x : Tm.BranchValue [X] (.var 0 : Tm Φ) X := .var rfl
  let pair := Tm.pair (.var 0) (.var 0) (Φ := Φ)
  let pre := Tm.liftSubstN 2 (replaceZero pair)
  let unpack := Tm.consSubst (.var 0) (Tm.singleSubst (.var 0 : Tm Φ))
  have hpre : Tm.Subst.HasType [product X X] [X] (replaceZero pair) := by
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact .pair x.hasType x.hasType
    | succ i => simp [At] at hi
  have hbody := (whiskerRightBody_typed X hr).hasType.substVars ((hpre.lift X).lift X)
  have step := Paper.Eqv.productBeta (.let₂Beta x x hbody)
  change Paper.Eqv [X] (.let₂ pair ((whiskerRightBody r).substVars pre))
    (((whiskerRightBody r).substVars pre).substVars unpack) [product A X] at step
  rw [show (Paper.RetainedLet.diagonal : Region Φ) = .br 0 pair from rfl, send_then]
  change Paper.Eqv [X] (.let₂ pair ((whiskerRightBody r).substVars pre)) _ _
  convert step using 1
  simp only [whiskerRightBody, substVars_comp, substVars_lsubst, substVars_renameVars]
  congr 1
  conv_lhs => rw [← substVars_var r]
  congr 1
  funext i
  cases i <;> rfl

private theorem retainedThenLeft {X A B : τ} {s : Region Φ} (hs : ValueBranches [X] s [B]) :
    Paper.Eqv [A, X] (seq (retain : Region Φ) ((whiskerLeftRegion s).renameVars (lift Nat.succ)))
      ((s.renameVars Nat.succ).lsubst (fun _ => finish)) [product A B] := by
  let a : Tm.BranchValue [A, X] (.var 0 : Tm Φ) A := .var rfl
  let x : Tm.BranchValue [A, X] (.var 1 : Tm Φ) X := .var rfl
  let pair := Tm.pair (.var 0) (.var 1) (Φ := Φ)
  let pre := Tm.liftSubstN 2 (replaceZero pair)
  let unpack := Tm.consSubst (.var 1) (Tm.singleSubst (.var 0 : Tm Φ))
  let ρ := lift (lift (lift Nat.succ))
  have hpre : Tm.Subst.HasType [product A X, X] [A, X] (replaceZero pair) := by
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact .pair a.hasType x.hasType
    | succ i =>
      cases i with
      | zero => cases Option.some.inj hi; exact x.hasType
      | succ i => simp [At] at hi
  have hbody := ((whiskerLeftBody_typed A hs).hasType.renameVars
    ((((Ren.wk [] X).lift (product A X)).lift A).lift X)).substVars
    ((hpre.lift A).lift X)
  have step := Paper.Eqv.productBeta (.let₂Beta a x hbody)
  change Paper.Eqv [A, X] (.let₂ pair (((whiskerLeftBody s).renameVars ρ).substVars pre))
    ((((whiskerLeftBody s).renameVars ρ).substVars pre).substVars unpack) [product A B] at step
  rw [send_then]
  change Paper.Eqv [A, X] (.let₂ pair (((whiskerLeftBody s).renameVars ρ).substVars pre)) _ _
  convert step using 1
  simp only [whiskerLeftBody, renameVars_lsubst, renameVars_comp, substVars_comp, substVars_lsubst,
    substVars_renameVars]
  congr 1
  rw [renameVars_eq_substVars]
  congr 1
  funext i
  cases i <;> rfl

private theorem pairedSyntax {X A B : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [A]) (hs : ValueBranches [X] s [B]) :
    Paper.Eqv [X]
      (seq (seq Paper.RetainedLet.diagonal (whiskerRightRegion r)) (whiskerLeftRegion s))
      (r.lsubst (fun _ => (s.renameVars Nat.succ).lsubst (fun _ => finish))) [product A B] := by
  have hkeep : LSubst.ValueFamily [X] [A] [product A X] (fun _ => (retain : Region Φ)) := by
    intro i D hi
    have e := List.mem_singleton.mp (List.mem_of_getElem? hi)
    subst D
    exact .br rfl (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))
  have hleft := seqValueBranches (Paper.RetainedLet.diagonal_typed (Φ := Φ) X)
    (whiskerRightRegion_typed X hr)
  have hk : LSubst.ValueFamily [] [product A X] [product A B] (fun _ => whiskerLeftRegion s) := by
    intro i D hi
    have e := List.mem_singleton.mp (List.mem_of_getElem? hi)
    subst D
    exact whiskerLeftRegion_typed A hs
  refine (Paper.Eqv.lsubstPost (rightOnDiagonal hr) hleft (hr.lsubst hkeep)
    (fun i D hi => (hk.liftVars X hi).hasType)).trans ?_
  change Paper.Eqv [X] ((r.lsubst (fun _ => retain)).lsubst (liftLSubstVars (fun _ => whiskerLeftRegion s))) _ _
  rw [lsubst_comp]
  apply Paper.lsubst_singleton_congr hr
  exact retainedThenLeft hs

private theorem finishReturn {X A B : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [A]) (hs : ValueBranches [X] s [B]) :
    Paper.Eqv [X]
      (r.lsubst (fun _ => (s.renameVars Nat.succ).lsubst (fun _ => finish)))
      (r.lsubst (fun _ => (s.renameVars Nat.succ).lsubst
        (fun _ => returnRegion (.pair (.var 1) (.var 0))))) [product A B] := by
  apply Paper.lsubst_singleton_congr hr
  apply Paper.lsubst_singleton_congr (hs.renameVars (Ren.wk [X] A))
  have h : Tm.BranchValue [B, A, X] (.pair (.var 1) (.var 0) : Tm Φ) (product A B) :=
    .pair (.var rfl) (.var rfl)
  exact (Paper.Eqv.cfgEta (.native (.base (returnRegion_branchValue h)))).symm

set_option backward.isDefEq.respectTransparency false in
theorem pairArrows_returnTerm {X A B : τ} {a b : Tm Φ}
    (ha : Tm.HasType [X] a A) (hb : Tm.HasType [X] b B) :
    pairArrows (returnTerm ha) (returnTerm hb) =
      returnTerm (.let₁ ha (.let₁ (hb.rename (Ren.wk [X] A))
        (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))) := by
  let hr := returnRegion_typed ha
  let hs := returnRegion_typed hb
  unfold pairArrows diagonalArrow returnTerm
  rw [← Category.assoc, whiskerRight_ofRegion, whiskerLeft_ofRegion]
  unfold tensorObj
  let hright := seqValueBranches (Paper.RetainedLet.diagonal_typed (Φ := Φ) X)
    (whiskerRightRegion_typed X hr)
  rw [ofRegion_comp _ _ hright, ofRegion_comp _ _ (seqValueBranches hright (whiskerLeftRegion_typed A hs))]
  apply (ofRegion_eq_iff _ _).2
  change Paper.Eqv [X] (seq (seq Paper.RetainedLet.diagonal (whiskerRightRegion (returnRegion a)))
    (whiskerLeftRegion (returnRegion b))) (returnRegion (.let₁ a
      (.let₁ (b.rename Nat.succ) (.pair (.var 1) (.var 0))))) [product A B]
  simpa only [returnRegion, returnRegion_rename] using (pairedSyntax hr hs).trans (finishReturn hr hs)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductReturn
