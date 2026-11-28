module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Evaluation
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Substitution

/-! # Observations under label renaming and guarded substitution
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Paper.BoundSimulation.Obstruction
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (UnitPayloadPolicy Env EnvTy Val ValTy Result ResultTy Frame FrameTy cfgRun
  cfgRun_mapOut finish enter step mapOut mapOut_loopResult mapTerminal shiftOut insideMap enter_insideMap
  finish_mapTerminalOn step_typed enter_typed mapOut_liftN liftLSubstN_local liftLSubstN_out)

universe u v

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

variable {observation : TermObservation (α := α) Φ}

local notation "evalTerm" => evalTermWith observation
local notation "evalRegion" => evalRegionWith observation

theorem evalRegion_renameLabels (r : Region Φ) (ρ : Nat → Nat) (env : Env) :
    evalRegion (r.renameLabels ρ) env = mapOut (fun i v => .jump (ρ i) v) (evalRegion r env) := by
  induction r generalizing ρ env with
  | br i t =>
    simp only [renameLabels, evalRegionWith]
    cases evalTerm t env <;> rfl
  | let₁ t r ih =>
    simp only [renameLabels, evalRegionWith]
    split
    · rfl
    · cases evalTerm t env with
      | none => rfl
      | some v => exact ih ρ _
  | let₂ t r ih =>
    simp only [renameLabels, evalRegionWith]
    split
    · rfl
    · cases evalTerm t env with
      | none => rfl
      | some v => cases v <;> first | rfl | exact ih ρ _
  | case t l r ihl ihr =>
    simp only [renameLabels, evalRegionWith]
    cases evalTerm t env with
    | none => rfl
    | some v => cases v <;> first | rfl | exact ihl ρ _ | exact ihr ρ _
  | cfg entry n bs ihe ihb =>
    simp only [renameLabels, evalRegionWith, ihe, ihb, mapOut_liftN]
    exact cfgRun_mapOut n _ _ _

theorem eval_liftLSubstVars (σ : Nat → Region Φ) (i : Nat) (env : Env) (u v : Val) :
    evalRegion (liftLSubstVars σ i) (extend (extend env u) v) = evalRegion (σ i) (extend env v) :=
  evalRegion_renameVars (σ i) (ρ := lift Nat.succ)
    (extend_rename (env := env) (env' := extend env u) (ρ := Nat.succ) (fun _ => rfl) v)

theorem mapOut_liftLSubstN (n : Nat) (σ : Nat → Region Φ) (env : Env) (r : Result) :
    mapOut (fun i v => evalRegion (liftLSubstN n σ i) (extend env v)) r =
      insideMap n (fun i v => evalRegion (σ i) (extend env v)) r := by
  cases r with
  | jump i v =>
    change evalRegion (liftLSubstN n σ i) (extend env v) =
      (if i < n then .jump i v else shiftOut n (evalRegion (σ (i - n)) (extend env v)))
    by_cases h : i < n
    · rw [ite_eq_left h, liftLSubstN_local n σ h]
      rfl
    · rw [ite_eq_right h]
      have he : liftLSubstN n σ i = (σ (i - n)).renameLabels (n + ·) := by
        have eq := liftLSubstN_out n σ (i - n)
        rwa [Nat.add_sub_of_le (Nat.le_of_not_gt h)] at eq
      rw [he, evalRegion_renameLabels]
      rfl
  | diverges => rfl
  | fault => rfl

set_option linter.concreteInstances false

variable [UnitPayloadPolicy]

theorem evalRegion_lsubst {Γ : VCtx (Ty α)} {r : Region Φ} {L : LCtx (Ty α)}
    (hr : ValueBranches Γ r L) {env : Env} (h : EnvTy Γ env) (σ : Nat → Region Φ) :
    evalRegion (r.lsubst σ) env = mapOut (fun i v => evalRegion (σ i) (extend env v)) (evalRegion r env) := by
  induction hr generalizing env σ with
  | br hi ht =>
    obtain ⟨v, eq, hv⟩ := evalValue (observation := observation) ht h
    rw [lsubst, evalRegion_subst _ (RealizesWith.single eq (value_not_computed ht)), evalRegionWith, eq]
    rfl
  | @let₁ _ t _ _ _ ht _ ih =>
    by_cases marked : (startsLet t && observation.boundUnaryLet) = true
    · simp [lsubst, evalRegionWith, marked, mapOut]
    · cases eq : evalTerm t env with
      | none => simp [lsubst, evalRegionWith, marked, eq, mapOut]
      | some v =>
        have hv := evalTerm_typed ht h eq
        simp only [lsubst, evalRegionWith, marked, Bool.false_eq_true, ite_false, eq]
        rw [ih (h.extend hv)]
        congr 1
        funext i w
        exact eval_liftLSubstVars σ i env v w
  | @let₂ _ t _ _ _ _ ht _ ih =>
    by_cases marked : (observation.computedRegionLet₂ && computes t) = true
    · simp [lsubst, evalRegionWith, marked, mapOut]
    · cases eq : evalTerm t env with
      | none => simp [lsubst, evalRegionWith, marked, eq, mapOut]
      | some v =>
        have hv := evalTerm_typed ht h eq
        cases hv with
        | pair h₁ h₂ =>
          simp only [lsubst, evalRegionWith, marked, Bool.false_eq_true, ite_false, eq]
          rw [ih ((h.extend h₁).extend h₂)]
          congr 1
          funext i w
          rw [eval_liftLSubstVars, eval_liftLSubstVars]
  | @case _ t _ _ _ _ _ ht _ _ il ir =>
    cases eq : evalTerm t env with
    | none => simp [lsubst, evalRegionWith, eq, mapOut]
    | some v =>
      have hv := evalTerm_typed ht h eq
      cases hv with
      | inl hv =>
        simp only [lsubst, evalRegionWith, eq]
        rw [il (h.extend hv)]
        congr 1
        funext i w
        exact eval_liftLSubstVars σ i env _ w
      | inr hv =>
        simp only [lsubst, evalRegionWith, eq]
        rw [ir (h.extend hv)]
        congr 1
        funext i w
        exact eval_liftLSubstVars σ i env _ w
  | @cfg n Δ e K bs R he hb ihe ihb =>
    let k := fun i v => evalRegion (σ i) (extend env v)
    let d := fun i v => evalRegion (bs i) (extend env v)
    let d' := fun i v =>
      evalRegion ((bs i).lsubst (liftLSubstVars (liftLSubstN n σ))) (extend env v)
    let start := evalRegion e env
    have hd (i : Fin n) (v : Val) (hv : ValTy v (R i)) : d' i v = insideMap n k (d i v) := by
      change evalRegion ((bs i).lsubst _) (extend env v) = _
      rw [ihb i (h.extend hv)]
      simp only [eval_liftLSubstVars, mapOut_liftLSubstN, k, d]
    have hc (s : Frame n) (hs : FrameTy R K s) :
        step d' (mapTerminal (mapOut k) s) = mapTerminal (mapOut k) (step d s) := by
      cases s with
      | inl r => rfl
      | inr s =>
        obtain ⟨i, v⟩ := s
        change enter n (d' i v) = mapTerminal (mapOut k) (enter n (d i v))
        rw [hd i v hs, enter_insideMap]
    let mark := markFeedback observation n
    change finish d' (enter n (evalRegion (e.lsubst (liftLSubstN n σ)) env)) mark =
      mapOut k (finish d (enter n start) mark)
    rw [ihe h, mapOut_liftLSubstN, enter_insideMap]
    exact finish_mapTerminalOn d d' (mapOut k) (mapOut_loopResult k mark) (FrameTy R K)
      (step_typed R K (fun i _ hv => evalRegion_typed (hb i).hasType (h.extend hv)))
      hc (enter n start) (enter_typed R (evalRegion_typed he.hasType h))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
