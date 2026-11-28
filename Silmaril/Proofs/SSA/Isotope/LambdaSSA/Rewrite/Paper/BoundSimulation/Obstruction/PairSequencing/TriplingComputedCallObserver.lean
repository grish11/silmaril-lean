module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseReturns

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallObserver

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Semantics (extend)
open Paper.BoundSimulation (boundLocalMap)
open Paper.WithCaseReturns.BinaryFold (FoldStep JoinedStep foldTerm)
open BoundSimulation.Obstruction.Observer
  (Val ValTy Env EnvTy Result ResultTy one onState one_eq_of_runs run_simulation mapOut)
open scoped Paper.BoundSimulation.Obstruction BoundSimulation.Obstruction.Observer.CanonicalUnit
open BoundSimulation.Obstruction.PairSequencing
  (projectionUnitSeed_same caseReturnJoin_same caseReturnSeed_same)
open BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith evalTermWith evalRegionWith evalRegion_typed evalRegion_lsubst
    eval_liftLSubstVars extension_same startsLet)

universe u v w
variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {observation : TermObservation (α := α) Φ} (unmarked : observation.caseTerm = false)

local notation "evalTerm" => evalTermWith observation
local notation "evalRegion" => evalRegionWith observation

private def untag : Val → Val
  | .inl v | .inr v => v
  | _ => .unit

include unmarked in
private theorem eval_fold {X : Ty α} {v : Val} (hv : ValTy v (.coprod X X)) (env : Env) :
    evalTerm (foldTerm (Φ := Φ)) (extend env v) = some (untag v) := by
  cases hv with
  | inl h => simp [evalTermWith, unmarked, extend, untag]
  | inr h => simp [evalTermWith, unmarked, extend, untag]

include unmarked in
private theorem eval_bound_fold {X : Ty α} {v : Val} (hv : ValTy v (.coprod X X)) (env : Env) :
    evalRegion (.let₁ (foldTerm (Φ := Φ)) (.br 0 (.var 0))) (extend env v) =
      Result.jump 0 (untag v) := by
  have shape : startsLet (foldTerm (Φ := Φ)) = false := rfl
  simp only [evalRegionWith, shape, Bool.false_and, Bool.false_eq_true, ite_false, eval_fold unmarked hv env]
  rfl

private theorem zero_payload {A : Ty α} {L : LCtx (Ty α)} {r : Result}
    (typed : ResultTy (A :: L) r) {v : Val} (eq : r = .jump 0 v) : ValTy v A := by
  rw [eq] at typed
  obtain ⟨T, hi, hv⟩ := typed
  cases Option.some.inj hi
  exact hv

include unmarked in
private theorem map_fold {X : Ty α} {L : LCtx (Ty α)} (env : Env) {r : Result}
    (typed : ResultTy (Silmaril.coprod X X :: L) r) :
    mapOut (fun i v => evalRegion (boundLocalMap (foldTerm (Φ := Φ)) i) (extend env v)) r =
      onState untag r := by
  cases r with
  | fault => rfl
  | diverges => rfl
  | jump i v =>
    cases i with
    | succ i => rfl
    | zero =>
      simp only [mapOut, onState, boundLocalMap, bindBranchArguments]
      exact eval_bound_fold unmarked (zero_payload typed rfl) env

include unmarked in
theorem foldStep_same {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {r s : Region Φ}
    (step : FoldStep pe Γ r s L) : SameWith observation Γ r s := by
  cases step with
  | @simulate _ X entry p q he hp hq square =>
    intro env henv
    let body := fun v => evalRegion p (extend env v)
    let body' := fun v => evalRegion q (extend env v)
    let start := evalRegion entry env
    change one body start = one body' (evalRegion (entry.lsubst (boundLocalMap foldTerm)) env)
    rw [evalRegion_lsubst he henv, map_fold unmarked env (evalRegion_typed he.hasType henv)]
    have stable (v w : Val) (hv : ValTy v (.coprod X X)) (eq : body v = .jump 0 w) :
        ValTy w (.coprod X X) :=
      zero_payload (evalRegion_typed hp.hasType (henv.extend hv)) eq
    have comm (v : Val) (hv : ValTy v (.coprod X X)) : body' (untag v) = onState untag (body v) := by
      have h := caseReturnJoin_same unmarked square _ (henv.extend hv)
      have lhs : evalRegion (p.lsubst (liftLSubstVars (boundLocalMap foldTerm))) (extend env v) =
          onState untag (body v) := by
        rw [evalRegion_lsubst hp (henv.extend hv)]
        simp only [eval_liftLSubstVars]
        exact map_fold unmarked env (evalRegion_typed hp.hasType (henv.extend hv))
      let ff := Paper.WithCaseReturns.BinaryFold.fold_typed (Φ := Φ) (Γ := Γ) X
      have ht : ValueBranches (Silmaril.coprod X X :: Γ)
          ((Region.br 0 (foldTerm (Φ := Φ))).bindBranchArguments) (X :: L) :=
        .let₁ ff (.br (ℓ := 0) rfl (.var rfl))
      rw [lhs, evalRegion_lsubst ht (henv.extend hv)] at h
      change onState untag (body v) = mapOut _ (evalRegion (.let₁ foldTerm (.br 0 (.var 0))) (extend env v)) at h
      rw [eval_bound_fold unmarked hv env] at h
      simpa only [mapOut, eval_liftLSubstVars, body'] using h.symm
    apply one_eq_of_runs
    intro r _
    exact run_simulation stable comm (fun _ => zero_payload (evalRegion_typed he.hasType henv))

include unmarked in
theorem binaryFold_same {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {r s : Region Φ}
    (eq : Paper.Extension.Eqv (JoinedStep pe) Γ r s L) : SameWith observation Γ r s :=
  extension_same (fun step => step.elim
    (fun old => old.elim projectionUnitSeed_same (caseReturnSeed_same unmarked)) (foldStep_same unmarked)) eq

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallObserver
