module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.TriplingComputedCallObserver
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallFeedback

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Semantics (extend extend_rename)
open Silmaril.DeBruijn (lift)
open Paper.WithCaseReturns.BinaryFold
  (JoinedStep ternaryStep ternaryFold ternaryFold_arrow ternaryFold_square)
open Paper.WithCaseReturns.BinaryFold.WithTripling (TriplingStep Step)
open Paper.Extension.Singleton
open Paper.Extension.Singleton.StructuralValues (inclusion)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open BoundSimulation.Obstruction.Observer
  (Val ValTy Env EnvTy Result ResultTy one onState one_eq_of_runs run_simulation mapOut)
open scoped Paper.BoundSimulation.Obstruction BoundSimulation.Obstruction.Observer.CanonicalUnit
open BoundSimulation.Obstruction.PairSequencing
  (projectionUnitSeed_same caseReturnSeed_same)
open BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith evalTermWith evalRegionWith evalRegion_typed evalRegion_lsubst
   evalRegion_renameVars evalRegion_substOn eval_liftLSubstVars extension_same startsLet)
open TriplingComputedCallObserver (binaryFold_same foldStep_same)

universe u v w
variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] (pe : ε)
  {observation : TermObservation (α := α) Φ}

local notation "TyS" => Ty α
set_option hygiene false in
local notation "S" => JoinedStep (τ := Ty α) (Φ := Φ) pe
local notation "Q" => TypeCategory S
local notation "Obj" => ofType S
local notation "Lit" => ofRegion S
local notation "π" => projection S
local notation "evalRegion" => evalRegionWith observation

@[expose] def env (v : Val) : Env := extend (fun _ => .unit) v

theorem env_typed {A : TyS} {v : Val} (hv : ValTy v A) : EnvTy [A] (env v) :=
  (show EnvTy ([] : VCtx TyS) (fun _ => .unit) from fun _ _ hi => by simp [At] at hi).extend hv

@[expose] noncomputable def observe (observation : TermObservation (α := α) Φ) (r : Region Φ) (v : Val) : Result :=
  evalRegionWith observation r (env v)

local notation "see" => observe observation

theorem observe_seq {A B : TyS} {r s : Region Φ} (hr : ValueBranches [A] r [B])
    {v : Val} (hv : ValTy v A) :
    see (compLSubst (fun _ => r) (fun _ => s) 0) v =
      mapOut (fun _ w => see s w) (see r v) := by
  unfold observe compLSubst
  rw [evalRegion_lsubst hr (env_typed hv)]
  congr 1
  funext i w
  exact eval_liftLSubstVars (fun _ => s) i (fun _ => .unit) v w

private theorem result_payload {A : TyS} {L : LCtx TyS} {r : Result}
    (typed : ResultTy (A :: L) r) {v : Val} (eq : r = .jump 0 v) : ValTy v A := by
  rw [eq] at typed
  obtain ⟨T, hi, hv⟩ := typed
  cases Option.some.inj hi
  exact hv

private theorem singleton_payload {A : TyS} {i : Nat} {v : Val}
    (typed : ResultTy [A] (.jump i v)) : i = 0 ∧ ValTy v A := by
  cases i with
  | zero => exact ⟨rfl, result_payload typed rfl⟩
  | succ i => obtain ⟨_, hi, _⟩ := typed; simp [At] at hi

theorem observe_case_left (l r : Region Φ) (v : Val) :
    see (.case (.var 0) (l.renameVars (lift Nat.succ)) (r.renameVars (lift Nat.succ))) (.inl v) =
      see l v := by
  unfold observe env
  simp only [evalRegionWith, evalTermWith]
  exact evalRegion_renameVars l (extend_rename (ρ := Nat.succ) (fun _ => rfl) v)

theorem observe_case_right (l r : Region Φ) (v : Val) :
    see (.case (.var 0) (l.renameVars (lift Nat.succ)) (r.renameVars (lift Nat.succ))) (.inr v) =
      see r v := by
  unfold observe env
  simp only [evalRegionWith, evalTermWith]
  exact evalRegion_renameVars r (extend_rename (ρ := Nat.succ) (fun _ => rfl) v)

@[expose] def route : Val → Result
  | .inl v => .jump 1 v
  | .inr v => .jump 0 v
  | _ => .fault

private def routeState (f : Val → Val) : Val → Result
  | .inl v => .jump 0 (.inl v)
  | .inr v => .jump 0 (.inr (f v))
  | _ => .fault

private theorem route_state (f : Val → Val) (r : Result) :
    mapOut (fun _ => route) (mapOut (fun _ => routeState f) r) =
      onState f (mapOut (fun _ => route) r) := by
  cases r with
  | fault | diverges => rfl
  | jump _ v => cases v <;> rfl

theorem observe_body {A B : TyS} {r : Region Φ}
    (hr : ValueBranches [A] r [Silmaril.coprod B A]) {v : Val} (hv : ValTy v A) :
    see (SyntacticCategory.iterationBody r) v = mapOut (fun _ => route) (see r v) := by
  unfold observe SyntacticCategory.iterationBody
  rw [evalRegion_lsubst hr (env_typed hv)]
  congr 1
  funext i x
  cases x <;> rfl

theorem observe_iterate (A : TyS) (r : Region Φ) (v : Val) :
    see (SyntacticCategory.iterateRegion A r) v =
      one (see (SyntacticCategory.iterationBody r)) (.jump 0 v) := by
  unfold observe SyntacticCategory.iterateRegion feedbackRegion cfgEntryContinuations
  simp only [evalRegionWith, evalTermWith]
  change one _ _ = one _ _
  congr 1
  funext w
  exact evalRegion_renameVars _ (extend_rename (ρ := Nat.succ) (fun _ => rfl) w)

private theorem observe_uniformity {A D B : TyS} {r s : Region Φ}
    (hr : ValueBranches [A] r [Silmaril.coprod B A])
    (hs : ValueBranches [D] s [Silmaril.coprod B D]) (f : Val → Val)
    (typed : ∀ v, ValTy v A → ValTy (f v) D)
    (square : ∀ v, ValTy v A → see s (f v) = mapOut (fun _ => routeState f) (see r v))
    {v : Val} (hv : ValTy v A) :
    see (SyntacticCategory.iterateRegion A r) v =
      see (SyntacticCategory.iterateRegion D s) (f v) := by
  rw [observe_iterate, observe_iterate]
  let body := see (SyntacticCategory.iterationBody r)
  let body' := see (SyntacticCategory.iterationBody s)
  have ht : ValueBranches [A] (SyntacticCategory.iterationBody r) [A, B] :=
    hr.lsubst (fun _ C hi =>
      (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸
        SyntacticCategory.iterationDispatch_valueBranches (Γ := [A]) A B)
  have stable (x y : Val) (hx : ValTy x A) (eq : body x = .jump 0 y) : ValTy y A := by
    exact result_payload (evalRegion_typed ht.hasType (env_typed hx)) eq
  have comm (x : Val) (hx : ValTy x A) : body' (f x) = onState f (body x) := by
    change see (SyntacticCategory.iterationBody s) (f x) = onState f (see (SyntacticCategory.iterationBody r) x)
    rw [observe_body hs (typed x hx), observe_body hr hx, square x hx, route_state]
  apply one_eq_of_runs
  intro out _
  exact run_simulation stable comm (fun _ h => by cases h; exact hv)

private theorem observe_congr (unmarked : observation.caseTerm = false)
    {A B : TyS} {r s : Region Φ} (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B])
    (eq : Lit hr = Lit hs) {v : Val} (hv : ValTy v A) : see r v = see s v :=
  binaryFold_same unmarked ((ofRegion_eq_iff S hr hs).mp eq) _ (env_typed hv)

private theorem representative {A B : TyS} (f : Obj A ⟶ Obj B) :
    ∃ (r : Region Φ) (hr : ValueBranches [A] r [B]), f = Lit hr := by
  obtain ⟨raw, rfl⟩ := (π).map_surjective f
  obtain ⟨r, hr, rfl⟩ := Paper.TypeCategory.exists_ofRegion raw
  exact ⟨r, hr, rfl⟩

private theorem lit_seq {A B D : TyS} {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [B] s [D]) :
    Lit (seqValueBranches hr hs) = Lit hr ≫ Lit hs :=
  (congrArg (π).map (Paper.TypeCategory.ofRegion_comp hr hs (seqValueBranches hr hs))).symm.trans
    ((π).map_comp _ _)

private theorem lit_iterate {A B : TyS} {r : Region Φ}
    (hr : ValueBranches [A] r [Silmaril.coprod B A]) :
    Lit (SyntacticCategory.iterateRegion_valueBranches hr) = iterateSum S (Lit hr) :=
  (congrArg (π).map (Paper.TypeCategory.iterateSum_ofRegion hr)).symm.trans
    (iterateSum_map S (Paper.TypeCategory.ofRegion hr)).symm

private theorem identity_typed (A : TyS) :
    ValueBranches [A] (.br 0 (.var 0) : Region Φ) [A] := .br rfl (.var (i := 0) rfl)

local infixr:65 " ⊕ₜ " => Silmaril.coprod

private def foldRegion : Region Φ :=
  .case (.var 0) (.br 0 (.var 0)) (.case (.var 0) (.br 0 (.var 0)) (.br 0 (.var 0)))

private theorem foldRegion_typed (A : TyS) : ValueBranches [A ⊕ₜ (A ⊕ₜ A)] (foldRegion (Φ := Φ)) [A] :=
  caseValueBranches (identity_typed A) (caseValueBranches (identity_typed A) (identity_typed A))

private theorem foldRegion_arrow (A : TyS) :
    Lit (foldRegion_typed A) = (inclusion S).map (ternaryFold pe A) := by
  have id : Lit (identity_typed A) = 𝟙 (Obj A) :=
    (congrArg (π).map (Paper.TypeCategory.ofRegion_id (Φ := Φ) A)).trans ((π).map_id _)
  rw [ternaryFold_arrow, ← id, exactCopair_ofRegion, exactCopair_ofRegion]
  rfl

private def foldVal : Val → Val
  | .inl v | .inr (.inl v) | .inr (.inr v) => v
  | _ => .unit

private theorem observe_fold {A : TyS} {v : Val} (hv : ValTy v (A ⊕ₜ (A ⊕ₜ A))) :
    see foldRegion v = .jump 0 (foldVal v) ∧ ValTy (foldVal v) A := by
  cases hv with
  | inl h => exact ⟨by simp [observe, foldRegion, env, evalRegionWith, evalTermWith, extend, foldVal], h⟩
  | inr h =>
    cases h with
    | inl h => exact ⟨by simp [observe, foldRegion, env, evalRegionWith, evalTermWith, extend, foldVal], h⟩
    | inr h => exact ⟨by simp [observe, foldRegion, env, evalRegionWith, evalTermWith, extend, foldVal], h⟩

private theorem left_typed (B D : TyS) :
    ValueBranches [B] (.br 0 (.inl (.var 0)) : Region Φ) [B ⊕ₜ D] :=
  .br rfl (.inl (.var (i := 0) rfl))

private theorem right_typed (B D : TyS) :
    ValueBranches [D] (.br 0 (.inr (.var 0)) : Region Φ) [B ⊕ₜ D] :=
  .br rfl (.inr (.var (i := 0) rfl))

private abbrev mapState (_B _A : TyS) :=
  Region.case (.var 0)
    ((Region.br 0 (.inl (.var 0)) : Region Φ).renameVars (lift Nat.succ))
    ((compLSubst (fun _ => foldRegion) (fun _ => Region.br 0 (.inr (.var 0))) 0).renameVars (lift Nat.succ))

private theorem mapState_typed (B A : TyS) :
    ValueBranches [B ⊕ₜ (A ⊕ₜ (A ⊕ₜ A))] (mapState (Φ := Φ) B A) [B ⊕ₜ A] :=
  caseValueBranches (left_typed (Φ := Φ) B A) (seqValueBranches (foldRegion_typed (Φ := Φ) A) (right_typed B A))

set_option backward.isDefEq.respectTransparency false in
private theorem exactMap (B A : TyS) :
    (sumIso S B (A ⊕ₜ (A ⊕ₜ A))).hom ≫
      coprod.map (𝟙 (Obj B)) ((inclusion S).map (ternaryFold pe A)) ≫ (sumIso S B A).inv =
      Lit (mapState_typed (Φ := Φ) B A) := by
  let h : Obj (A ⊕ₜ (A ⊕ₜ A)) ⟶ Obj A := (inclusion S).map (ternaryFold pe A)
  have rep : exactCopair S (sumCofan S B A).inl (h ≫ (sumCofan S B A).inr) =
      Lit (mapState_typed (Φ := Φ) B A) := calc
    _ = exactCopair S (Lit (left_typed B A))
        (Lit (seqValueBranches (foldRegion_typed A) (right_typed B A))) := by
      have left : (sumCofan S B A).inl = Lit (left_typed B A) :=
        congrArg (π).map (Paper.TypeCategory.sumCofan_inl (Φ := Φ) B A)
      have right : (sumCofan S B A).inr = Lit (right_typed B A) :=
        congrArg (π).map (Paper.TypeCategory.sumCofan_inr (Φ := Φ) B A)
      rw [lit_seq pe (foldRegion_typed A) (right_typed B A), foldRegion_arrow pe A, ← left, ← right]
    _ = _ := exactCopair_ofRegion S (left_typed B A)
      (seqValueBranches (foldRegion_typed A) (right_typed B A))
  change (sumIso S B (A ⊕ₜ (A ⊕ₜ A))).hom ≫
    coprod.map (𝟙 (Obj B)) h ≫ (sumIso S B A).inv = Lit (mapState_typed (Φ := Φ) B A)
  rw [← rep]
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit S B (A ⊕ₜ (A ⊕ₜ A)))
  · rw [← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_map_assoc, Category.id_comp,
      ← sumCofan_inl_sumIso_hom S B A, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact ((sumCofanIsColimit S B (A ⊕ₜ (A ⊕ₜ A))).fac
      (BinaryCofan.mk (sumCofan S B A).inl (h ≫ (sumCofan S B A).inr)) ⟨WalkingPair.left⟩).symm
  · rw [← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_map_assoc,
      ← sumCofan_inr_sumIso_hom S B A, Category.assoc (sumCofan S B A).inr,
      Iso.hom_inv_id, Category.comp_id]
    exact ((sumCofanIsColimit S B (A ⊕ₜ (A ⊕ₜ A))).fac
      (BinaryCofan.mk (sumCofan S B A).inl (h ≫ (sumCofan S B A).inr)) ⟨WalkingPair.right⟩).symm

private theorem observe_mapState {B A : TyS} {v : Val} (hv : ValTy v (B ⊕ₜ (A ⊕ₜ (A ⊕ₜ A)))) :
    see (mapState (Φ := Φ) B A) v = routeState foldVal v := by
  cases hv with
  | inl h =>
    rw [observe_case_left]
    simp [observe, env, evalRegionWith, evalTermWith, startsLet, extend, routeState]
  | inr h =>
    rw [observe_case_right, observe_seq (foldRegion_typed A) h, (observe_fold h).1]
    simp [observe, env, evalRegionWith, evalTermWith, startsLet, extend, routeState, mapOut]

set_option backward.isDefEq.respectTransparency false in
theorem triplingStep_same (unmarked : observation.caseTerm = false)
    {Γ L : List TyS} {r s : Region Φ} (step : TriplingStep pe Γ r s L) :
    SameWith observation Γ r s := by
  cases step with
  | @uniform A B g r s hr hs left right =>
    let P := A ⊕ₜ (A ⊕ₜ A)
    let h : Obj P ⟶ Obj A := (inclusion S).map (ternaryFold pe A)
    let step := ternaryStep pe g
    obtain ⟨p, hp, hpEq⟩ := representative pe (step ≫ (sumIso S B P).inv)
    obtain ⟨q, hq, hqEq⟩ := representative pe (g ≫ (sumIso S B A).inv)
    have square : Lit (seqValueBranches hp (mapState_typed B A)) =
        Lit (seqValueBranches (foldRegion_typed A) hq) := by
      rw [lit_seq pe hp (mapState_typed B A), lit_seq pe (foldRegion_typed A) hq,
        ← hpEq, ← hqEq, ← exactMap pe B A, foldRegion_arrow]
      change (step ≫ (sumIso S B P).inv) ≫
        (sumIso S B P).hom ≫ coprod.map (𝟙 (Obj B)) h ≫ (sumIso S B A).inv =
        h ≫ g ≫ (sumIso S B A).inv
      rw [Category.assoc, Iso.inv_hom_id_assoc]
      simpa only [Category.assoc, step, h] using
        congrArg (· ≫ (sumIso S B A).inv) (ternaryFold_square pe g)
    have sim (v : Val) (hv : ValTy v P) :
        see q (foldVal v) = mapOut (fun _ => routeState foldVal) (see p v) := by
      have eq := observe_congr pe unmarked (seqValueBranches hp (mapState_typed B A))
        (seqValueBranches (foldRegion_typed A) hq) square hv
      change see (compLSubst (fun _ => p) (fun _ => mapState B A) 0) v =
        see (compLSubst (fun _ => foldRegion) (fun _ => q) 0) v at eq
      rw [observe_seq hp hv, observe_seq (foldRegion_typed A) hv, (observe_fold hv).1] at eq
      simp only [mapOut] at eq
      rw [← eq]
      cases output : see p v with
      | fault | diverges => rfl
      | jump i w =>
        have typed := evalRegion_typed (observation := observation) hp.hasType (env_typed hv)
        change ResultTy [B ⊕ₜ P] (see p v) at typed
        rw [output] at typed
        exact observe_mapState (singleton_payload typed).2
    have leftEq : Lit hr = Lit (SyntacticCategory.iterateRegion_valueBranches hp) := by
      rw [left, lit_iterate pe hp, ← hpEq]
      rfl
    have rightEq : Lit hs = Lit (seqValueBranches (foldRegion_typed A)
        (SyntacticCategory.iterateRegion_valueBranches hq)) := by
      rw [right, lit_seq pe (foldRegion_typed A) (SyntacticCategory.iterateRegion_valueBranches hq),
        foldRegion_arrow pe A, lit_iterate pe hq, ← hqEq]
      rfl
    intro any typed
    let state := any 0
    have hv : ValTy state P := typed (rfl : At [P] 0 P)
    have envAgree : ∀ i D, At [P] i D → any i = env state i := by
      intro i D hi
      cases i with
      | zero => rfl
      | succ i => simp [At] at hi
    have changed (r : Region Φ) (ht : HasType [P] r [B]) :
        evalRegion r any = see r state := by
      simpa only [substVars_var, observe] using
        evalRegion_substOn (observation := observation) ht (θ := Tm.var)
          (fun i D hi => ⟨congrArg some (envAgree i D hi), rfl⟩)
    rw [changed _ hr.hasType, changed _ hs.hasType,
      observe_congr pe unmarked hr _ leftEq hv, observe_congr pe unmarked hs _ rightEq hv]
    change _ = see (compLSubst (fun _ => foldRegion)
      (fun _ => SyntacticCategory.iterateRegion A q) 0) state
    rw [observe_seq (foldRegion_typed A) hv, (observe_fold hv).1, mapOut]
    exact observe_uniformity hp hq foldVal (fun _ w => (observe_fold (observation := observation) w).2) sim hv

theorem withTriplingSeed_same (unmarked : observation.caseTerm = false) {Γ L : List TyS} {r s : Region Φ}
    (step : Step (τ := TyS) (Φ := Φ) pe Γ r s L) : SameWith observation Γ r s :=
  step.elim
    (fun old => old.elim
      (fun cases => cases.elim projectionUnitSeed_same (caseReturnSeed_same unmarked))
      (foldStep_same unmarked)) (triplingStep_same pe unmarked)

theorem withTripling_same (unmarked : observation.caseTerm = false) {Γ L : List TyS} {r s : Region Φ}
    (eq : Paper.Extension.Eqv (Step (τ := TyS) (Φ := Φ) pe) Γ r s L) :
    SameWith observation Γ r s :=
  extension_same (withTriplingSeed_same pe unmarked) eq

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallFeedback
