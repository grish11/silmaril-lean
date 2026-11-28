module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.CapturedSquare.Thms

/-! # The capture embedding square for the guarded one-block endpoint -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.SingletonReification.SingleCfg
open Silmaril.DeBruijn (lift)
open CfgEta (singleCfg reentry)
open CfgEta.Uniformity (localMap)
open CfgEta.TypeCategory (whiskerLeftBody whiskerLeftBody_typed whiskerLeftRegion
  whiskerLeftRegion_typed seqValueBranches singletonValueFamily)
open CfgEta.TypeCategory.Retained (distributorRegion)
open Paper.RetainedLet (diagonal diagonal_typed unpackBody)
open Paper.BoundSimulation.CapturedSquare (applyPacked_unpackBody packedStep_typed unpackBody_valueBranches)
open Paper.PackedBody (applyPacked)
open Paper.RetainedCase (assembleCase routeCase boundCase boundCase_typed packedArms
  routeCase_typed route_normalizes)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X S D : τ}


omit [TypeFormers τ] [HasTy Φ τ] in
private theorem lift_agrees {Γ : VCtx τ} {T : τ} {θ υ : Nat → Tm Φ}
    (h : ∀ ⦃i A⦄, At Γ i A → θ i = υ i) :
    ∀ ⦃i A⦄, At (T :: Γ) i A → Tm.liftSubst θ i = Tm.liftSubst υ i := by
  intro i A hi
  cases i with
  | zero => rfl
  | succ i => exact congrArg (Tm.rename Nat.succ) (h (show At Γ i A from hi))

theorem region_subst_eq {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : HasType Γ r L) {θ υ : Nat → Tm Φ}
    (h : ∀ ⦃i A⦄, At Γ i A → θ i = υ i) : r.substVars θ = r.substVars υ := by
  induction hr generalizing θ υ with
  | br _ ha => rw [Region.substVars, Region.substVars, Paper.RetainedLet.term_subst_eq ha (fun _ _ hi => h hi)]
  | let₁ ha _ ih => rw [Region.substVars, Region.substVars, Paper.RetainedLet.term_subst_eq ha (fun _ _ hi => h hi), ih (lift_agrees h)]
  | let₂ ha _ ih =>
    simp only [Region.substVars, Tm.liftSubstN, Paper.RetainedLet.term_subst_eq ha (fun _ _ hi => h hi),
      ih (lift_agrees (lift_agrees h))]
  | case ha _ _ il ir =>
    rw [Region.substVars, Region.substVars, Paper.RetainedLet.term_subst_eq ha (fun _ _ hi => h hi),
      il (lift_agrees h), ir (lift_agrees h)]
  | cfg R _ _ ie ib =>
    rw [Region.substVars, Region.substVars, ie h]
    congr 1
    funext i
    exact ib i (lift_agrees h)

theorem singleton_subst {P : τ} {L : LCtx τ} {r : Region Φ} (hr : HasType [P] r L)
    {θ υ : Nat → Tm Φ} (h : θ 0 = υ 0) : r.substVars θ = r.substVars υ := by
  apply region_subst_eq hr
  intro i A hi
  cases i with
  | zero => exact h
  | succ i => simp [At] at hi

private theorem singleton_rename {P : τ} {L : LCtx τ} {r : Region Φ} (hr : HasType [P] r L)
    {ρ υ : Nat → Nat} (h : ρ 0 = υ 0) : r.renameVars ρ = r.renameVars υ := by
  simp only [renameVars_eq_substVars]
  exact singleton_subst hr (congrArg Tm.var h)

omit [HasTy Φ τ] in
theorem capturePair_typed :
    Tm.BranchValue [S, X] (capturePair : Tm Φ) (Silmaril.product X S) :=
  .pair (.var (i := 1) rfl) (.var (i := 0) rfl)

private theorem embed_family :
    LSubst.ValueFamily (Φ := Φ) [X] [S, D] [Silmaril.product X S, D] (localMap capturePair) := by
  intro i A h
  cases i with
  | zero =>
    cases Option.some.inj h
    exact .br rfl capturePair_typed
  | succ i =>
    exact .br h (.var (i := 0) rfl)

private theorem carryRepeat_typed {p : Region Φ} (hp : ValueBranches [S, X] p [S, D]) :
    ValueBranches [S, X] (p.lsubst carryRepeat) [Silmaril.product X S, D] :=
  hp.lsubst (embed_family.liftVars S)

private theorem carryEntry_typed {e : Region Φ} (he : ValueBranches [X] e [S, D]) :
    ValueBranches [X] (carryEntry e) [Silmaril.product X S, D] :=
  he.lsubst embed_family

theorem carryBlock_typed {p : Region Φ} (hp : ValueBranches [S, X] p [S, D]) :
    ValueBranches [Silmaril.product X S] (carryBlock p) [Silmaril.product X S, D] :=
  packedStep_typed hp

set_option backward.isDefEq.respectTransparency false in
theorem capture_square {p : Region Φ} (hp : ValueBranches [S, X] p [S, D]) :
    Paper.Eqv [S, X]
      (p.lsubst carryRepeat)
      ((Region.br 0 capturePair).lsubst (liftLSubstVars (fun _ => carryBlockInCfg p)))
      [Silmaril.product X S, D] := by
  have embed : (Region.br 0 capturePair).lsubst (liftLSubstVars (fun _ => carryBlockInCfg p)) =
      applyPacked (carryBlock p) := by
    simp only [lsubst, liftLSubstVars, carryBlockInCfg, renameVars_comp, substVars_renameVars, applyPacked]
    congr 1
    funext i
    cases i <;> rfl
  rw [embed]
  exact (applyPacked_unpackBody (carryRepeat_typed hp)).symm

set_option backward.isDefEq.respectTransparency false in
theorem move_capture {e p : Region Φ} (he : ValueBranches [X] e [S, D])
    (hp : ValueBranches [S, X] p [S, D]) :
    Paper.Eqv [X] (singleCfg e p) (singleCfg (carryEntry e) (carryBlockInCfg p)) [D] :=
  .uniform he hp ((carryBlock_typed hp).renameVars ((Ren.wk [] X).lift (Silmaril.product X S))).hasType
    capturePair_typed (capture_square hp)

set_option backward.isDefEq.respectTransparency false in
private theorem dispatch_carried {P : τ} {e q : Region Φ} (he : ValueBranches [X] e [P, D])
    (hq : ValueBranches [P] q [P, D]) :
    Paper.Eqv [X] (singleCfg e (q.renameVars (lift Nat.succ))) (e.lsubst (carriedDispatch P q)) [D] := by
  have hw := hq.renameVars ((Ren.wk [] X).lift P)
  refine (Paper.Eqv.cfgEta (CfgEta.Eqv.eta he hw)).trans (.lsubstCongr he ?_)
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    have eq : (q.renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ)) =
        (q.renameVars (lift Nat.succ)).renameVars (lift Nat.succ) := by
      simp only [renameVars_comp]
      exact singleton_rename hq.hasType rfl
    simp only [reentry, carriedDispatch, feedbackRegion, cfgEntryContinuations,
      List.length_cons, List.length_nil, Region.renameVars, Tm.rename, eq]
    exact .refl (.cfg (fun _ : Fin 1 => P) (.br (ℓ := 0) rfl (.var (i := 0) rfl))
      (fun _ => (hw.renameVars ((Ren.wk [X] P).lift P)).hasType))
  | succ i =>
    have h := Paper.Eqv.cfgEta (.native (.base (.entry
      (.cfgBrExit (fun _ : Fin 1 => P) (show At [D] i A from hi)
        (.var (i := 0) (show At [A, X] 0 A from rfl))
        (fun _ => (hw.renameVars ((Ren.wk [X] A).lift P)).hasType)))))
    simpa only [reentry, cfgEntryContinuations, carriedDispatch, Nat.zero_add, Nat.one_add] using h

set_option backward.isDefEq.respectTransparency false in
theorem guardedCfg_carried {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    Paper.Eqv [X] (guardedCfg S D e b)
      ((carryEntry (decodeExits e [S, D])).lsubst
        (carriedDispatch (Silmaril.product X S) (carryBlock (decodeExits (Paper.PackedBody.applyPacked b) [S, D])))) [D] := by
  let he' := decodeExits_typed he
  let hb' := decodeExits_typed (Paper.PackedBody.applyPacked_typed hb)
  exact (move_capture he' hb').trans (dispatch_carried (carryEntry_typed he') (carryBlock_typed hb'))

set_option backward.isDefEq.respectTransparency false in
theorem decodeExits_eq_lsubst {Γ : VCtx τ} {L : LCtx τ} {e : Region Φ}
    (he : ValueBranches Γ e [packedExitType L]) :
    Paper.Eqv Γ (decodeExits e L) (e.lsubst (fun _ => unpackExits L)) L := by
  let P := packedExitType L
  let dec : Region Φ := unpackExits L
  let R : Fin 1 → τ := fun _ => P
  let labels : Nat → Nat := Nat.succ
  have head : Ren [P] (P :: L) id := by
    intro i A hi
    cases i with
    | zero => exact hi
    | succ i => simp [At] at hi
  have he' : ValueBranches Γ e (P :: L) := by
    rw [← renameLabels_id e, renameLabels_eq_lsubst]
    exact he.lsubst (fun _ _ hi => .br (head hi) (.var rfl))
  have hd : ValueBranches (P :: Γ) dec L := (unpackExits_valueFamily Γ L) (ℓ := 0) (A := P) rfl
  have hb : ValueBranches (P :: Γ) (dec.renameLabels labels) (P :: L) := by
    rw [renameLabels_eq_lsubst]
    exact hd.lsubst (fun _ _ hi => .br ((Ren.wk L P) hi) (.var rfl))
  have shape : decodeExits e L = singleCfg e (dec.renameLabels labels) := by
    simp only [decodeExits, linkExits, singleCfg, List.length_cons, List.length_nil, Nat.zero_add, Nat.one_add, labels, dec]
  rw [shape]
  apply (Paper.Eqv.cfgEta (CfgEta.Eqv.eta he' hb)).trans
  exact .lsubstCongr he (by
    intro i A hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      let wk := (Ren.wk Γ P).lift P
      have hblock : HasType (P :: P :: Γ)
          ((dec.renameLabels labels).renameVars (lift Nat.succ)) (P :: L) := hb.hasType.renameVars wk
      have enter := Paper.Eqv.cfgEta (.native (.base (.entry
        (.cfgBrLocal R 0 (.var (i := 0) (show At (P :: Γ) 0 P from rfl)) (fun _ => hblock)))))
      have beta : Paper.Eqv (P :: Γ)
          (.let₁ (.var 0) ((dec.renameLabels labels).renameVars (lift Nat.succ)))
          (dec.renameLabels labels) (P :: L) := by
        have h := Paper.Eqv.cfgEta (.native (.letValue
          (.var (i := 0) (show At (P :: Γ) 0 P from rfl)) hblock))
        have cancel (r : Region Φ) :
            (r.renameVars (lift Nat.succ)).substVars (Tm.singleSubst (.var 0)) = r :=
          congrFun (compLSubst_id_left (fun _ => r)) 0
        rw [cancel] at h
        exact h
      have inside := Paper.Eqv.cfg R beta (fun _ => Paper.Eqv.refl hblock)
      have out := Paper.Eqv.cfgEta (.native (.cfgOutward R hd.hasType (fun _ => hblock)))
      simp only [Nat.zero_add, Nat.one_add] at out
      exact enter.trans (inside.trans out)
    | succ i => simp [At] at hi)

private def retainInput {Φ : Type v} : Nat → Region Φ :=
  fun _ => .br 0 (.pair (.var 1) (.var 0))

private theorem retainInput_typed (X A : τ) :
    LSubst.ValueFamily (Φ := Φ) [X] [A] [Silmaril.product X A] retainInput := by
  intro i B hi
  cases List.mem_singleton.mp (List.mem_of_getElem? hi)
  exact .br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))

set_option backward.isDefEq.respectTransparency false in
private theorem duplicate_whisker {A : τ} {p : Region Φ} (hp : ValueBranches [X] p [A]) :
    Paper.Eqv [X] (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion p) 0)
      (p.lsubst retainInput) [Silmaril.product X A] := by
  let P := Silmaril.product X X
  let t := Tm.pair (.var 0) (.var 0) (Φ := Φ)
  let σ := Tm.liftSubstN 2 (Tm.singleSubst t)
  let κ := Tm.consSubst (.var 0) (Tm.singleSubst (.var 0 : Tm Φ))
  let b := whiskerLeftBody p
  let υ := lift (lift (lift Nat.succ))
  have ht : Tm.HasType [X] t P := .pair (.var (i := 0) rfl) (.var (i := 0) rfl)
  have hb : Region.HasType [X, X, X] ((b.renameVars υ).substVars σ) [Silmaril.product X A] :=
    ((whiskerLeftBody_typed X hp).hasType.renameVars
      ((((Ren.wk [] X).lift P).lift X).lift X)).substVars
      (((Tm.Subst.HasType.single ht).lift X).lift X)
  have hβ := Paper.Eqv.productBeta (.let₂Beta (.var (i := 0) (rfl : At [X] 0 X))
    (.var (i := 0) (rfl : At [X] 0 X)) hb)
  change Paper.Eqv [X] (.let₂ t ((b.renameVars υ).substVars σ))
    (((b.renameVars υ).substVars σ).substVars κ) [Silmaril.product X A] at hβ
  have eq : ((b.renameVars υ).substVars σ).substVars κ = p.lsubst retainInput := by
    rw [substVars_comp, substVars_renameVars]
    dsimp only [b, whiskerLeftBody]
    rw [substVars_lsubst, substVars_renameVars]
    have ep : p.substVars (((fun i => (σ i).subst κ) ∘ υ) ∘ lift (Nat.succ ∘ Nat.succ)) = p := by
      refine (singleton_subst hp.hasType (υ := Tm.var) ?_).trans (substVars_var p)
      rfl
    rw [ep]
    rfl
  rw [eq] at hβ
  exact hβ

set_option backward.isDefEq.respectTransparency false in
private theorem recover_pair {T : τ} {r : Region Φ} (hr : ValueBranches [T, X] r [D]) :
    Paper.Eqv [T, X]
      (((unpackBody r).renameVars (lift Nat.succ)).substVars (Tm.singleSubst capturePair)) r [D] := by
  have recover : (((unpackBody r).renameVars (lift Nat.succ)).substVars (Tm.singleSubst capturePair)) =
      applyPacked (unpackBody r) := by
    rw [substVars_renameVars, applyPacked]
    exact singleton_subst (unpackBody_valueBranches hr).hasType rfl
  rw [recover]
  exact applyPacked_unpackBody hr

set_option backward.isDefEq.respectTransparency false in
private theorem assembleCase_lsubst {A B : τ} {p l r : Region Φ}
    (hp : ValueBranches [X] p [Silmaril.coprod A B])
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.Eqv [X] (assembleCase p l r) (p.lsubst (fun _ => boundCase l r)) [D] := by
  let T := Silmaril.coprod A B
  let P := Silmaril.product X T
  let first := compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion p) 0
  let route := routeCase l r
  have hfirst := seqValueBranches (diagonal_typed (Φ := Φ) X) (whiskerLeftRegion_typed X hp)
  have hroute := routeCase_typed hl hr
  have hpaired := hp.lsubst (retainInput_typed X T)
  have head := (duplicate_whisker hp).lsubstPost hfirst hpaired
    (fun _ _ hi => (((singletonValueFamily hroute).liftVars X) hi).hasType)
  have endpoint : Paper.Eqv [X] (assembleCase p l r)
      ((p.lsubst retainInput).lsubst (fun _ => route.renameVars (lift Nat.succ))) [D] := by
    unfold assembleCase
    rw [compLSubst_assoc]
    exact head
  apply endpoint.trans
  rw [lsubst_comp]
  apply Paper.Eqv.lsubstCongr hp
  intro i C hi
  cases List.mem_singleton.mp (List.mem_of_getElem? hi)
  have weaken : (route.renameVars (lift Nat.succ)).renameVars (lift Nat.succ) =
      route.renameVars (lift Nat.succ) := by
    rw [renameVars_comp]
    exact singleton_rename hroute.hasType rfl
  simp only [compLSubst, retainInput, lsubst, liftLSubstVars, weaken]
  change Paper.Eqv [T, X] (((route.renameVars (lift Nat.succ))).substVars (Tm.singleSubst capturePair))
    (boundCase l r) [D]
  have ren := (Ren.wk ([] : VCtx τ) T).lift P
  have switch := (route_normalizes hl hr).renameVars ren
  have σ : ∀ ⦃i U⦄, At [P, T] i U →
      Tm.BranchValue [T, X] (Tm.singleSubst (capturePair : Tm Φ) i) U := by
    intro i U h
    cases i with
    | zero =>
      cases Option.some.inj h
      exact capturePair_typed
    | succ i => exact .var (show At [T, X] i U from (by
        cases i with
        | zero => simp [At] at h ⊢; exact h
        | succ i => simp [At] at h))
  exact (switch.substVars σ).trans (recover_pair (boundCase_typed hl hr))

set_option backward.isDefEq.respectTransparency false in
theorem guardedCfg_exitContinuation {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    Paper.Eqv [X] (guardedCfg S D e b)
      (e.lsubst (fun _ => carriedExitContinuation X S D b)) [D] := by
  let P := Silmaril.product X S
  let q := carryBlock (decodeExits (Paper.PackedBody.applyPacked b) [S, D])
  have decoded := decodeExits_typed (L := [S, D]) he
  have literal := he.lsubst (unpackExits_valueFamily [X] [S, D])
  have d := decodeExits_eq_lsubst he (L := [S, D])
  have qtyped := carryBlock_typed (decodeExits_typed (L := [S, D]) (Paper.PackedBody.applyPacked_typed hb))
  have e₁ := d.lsubstPost decoded literal (fun _ _ hi => (embed_family (X := X) (S := S) (D := D) hi).hasType)
  have old := carryEntry_typed decoded
  have new := carryEntry_typed literal
  have hdispatch : LSubst.HasType [X] [P, D] [D] (carriedDispatch P q) := by
    intro i A hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      let wk := (Ren.wk [] X).lift P
      let w := (Ren.wk [X] P).lift P
      have same : (q.renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ)) =
          q.renameVars (lift Nat.succ) := by
        rw [renameVars_comp]
        exact singleton_rename qtyped.hasType rfl
      simp only [carriedDispatch, feedbackRegion, cfgEntryContinuations,
        List.length_cons, List.length_nil, Region.renameVars, Tm.rename, same]
      have hh := HasType.cfg (fun _ : Fin 1 => P)
        (.br (ℓ := 0) rfl (.var (i := 0) rfl))
        (fun _ => (qtyped.renameVars (wk.comp w)).hasType)
      have ep : q.renameVars (lift Nat.succ ∘ lift Nat.succ) = q.renameVars (lift Nat.succ) :=
        singleton_rename qtyped.hasType rfl
      rw [← ep]
      exact hh
    | succ i => exact .br (show At [D] i A from hi) (.var (i := 0) rfl)
  have e₂ := e₁.lsubstPost old new hdispatch
  refine (guardedCfg_carried he hb).trans ?_
  simp only [carryEntry, lsubst_comp, carriedExitContinuation] at e₂ ⊢
  have hc :
      compLSubst (compLSubst (fun _ => unpackExits [S, D]) (localMap capturePair)) (carriedDispatch P q) =
        (fun _ => carriedExitContinuation X S D b) := by
    rw [compLSubst_assoc]
    rfl
  change Paper.Eqv [X] ((decodeExits e [S, D]).lsubst _)
    (e.lsubst (fun _ => carriedExitContinuation X S D b)) [D]
  rw [← hc]
  exact e₂

set_option backward.isDefEq.respectTransparency false in
theorem canonicalRegion_exitContinuation {e step : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hs : ValueBranches [Silmaril.product X S] step
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)]) :
    Paper.Eqv [X] (canonicalRegion X S e step)
      (e.lsubst (fun _ => canonicalExitContinuation X S step)) [D] := by
  let drop := CfgEta.TypeCategory.productSndBranches (Φ := Φ) X D
  have arms := assembleCase_lsubst (seqValueBranches he (exitDecoder_typed S D))
    (Paper.PackedBody.applyPacked_typed drop)
    (Paper.PackedBody.applyPacked_typed (seqValueBranches (SyntacticCategory.iterateRegion_valueBranches hs) drop))
  change Paper.Eqv [X] (canonicalRegion X S e step)
    (((e.lsubst (fun _ => (exitDecoder (τ := τ)).renameVars (lift Nat.succ))).lsubst _)) [D] at arms
  rw [lsubst_comp] at arms
  exact arms

set_option backward.isDefEq.respectTransparency false in
theorem canonicalRegion_eq_guardedCfg_of_exitContinuation {e b step : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]])
    (hs : ValueBranches [Silmaril.product X S] step
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)])
    (localEq : Paper.Eqv [packedExitType [S, D], X]
      (canonicalExitContinuation X S step) (carriedExitContinuation X S D b) [D]) :
    Paper.Eqv [X] (canonicalRegion X S e step) (guardedCfg S D e b) [D] :=
  (canonicalRegion_exitContinuation he hs).trans
    ((Paper.lsubst_singleton_congr he localEq).trans (guardedCfg_exitContinuation he hb).symm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgEndpoint
