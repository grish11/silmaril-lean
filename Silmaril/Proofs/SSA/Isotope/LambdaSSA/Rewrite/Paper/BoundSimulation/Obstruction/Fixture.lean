module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Soundness
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms

/-! # The closed and categorical uniformity counterexamples
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory Paper.BoundSimulation
open Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction
open Observer
open scoped Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction
open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.AlternateUnit

private theorem guardedRepeat (U : Ty Empty) (Γ : VCtx (Ty Empty)) :
    ValueBranches (U :: Γ) repeatBody [U, result] :=
  .br (ℓ := 0) rfl (.var (i := 0) rfl)

theorem local_square : Paper.Eqv [state] localSource localTarget [result, result] := by
  unfold localSource localTarget
  rw [lsubst_bindBranchArguments_br]
  exact .refl (.let₁ state_typed (.br (ℓ := 0) rfl (.var (i := 0) rfl)))

theorem opt_in_equality : Paper.Extension.Eqv InstructionFreeStep [] before after [result] := by
  let : HasEff Empty Bool := ⟨fun _ => true⟩
  have he : ValueBranches [] entry [state, result] := .br (ℓ := 0) rfl (.inl .unit)
  have seed : InstructionFreeStep [] before after [result] :=
    .simulate he (guardedRepeat state []) (guardedRepeat result []) state_typed
      (.let₁ .var .unit) local_square
  exact .extra seed.typed.1 seed.typed.2 seed

private theorem repeatTag_typed (A : Ty Empty) :
    ValueBranches [A] (.br 0 (.inr (.var 0)) : Region Empty) [Silmaril.coprod result A] :=
  .br (ℓ := 0) rfl (.inr (.var (i := 0) rfl))


set_option backward.isDefEq.respectTransparency false in
private theorem iterateRepeat (A : Ty Empty) :
    iterate (Y := ofType result) (X := ofType (Φ := Empty) A) coprod.inr =
      ofRegion (SyntacticCategory.iterateRegion_valueBranches (repeatTag_typed A)) := by
  have hin : (coprod.inr : ofType (Φ := Empty) A ⟶ ofType result ⨿ ofType A) ≫
      (sumIso (Φ := Empty) result A).inv = (sumCofan (Φ := Empty) result A).inr := by
    rw [← sumCofan_inr_sumIso_hom result A, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change iterateSum (coprod.inr ≫ (sumIso (Φ := Empty) result A).inv) = _
  rw [hin, sumCofan_inr]
  exact iterateSum_ofRegion (repeatTag_typed A)

private theorem repeatDiverges (v : Val) :
    finish (fun (_ : Fin 1) w => .jump 0 w) (.inr (0, v)) = .diverges := by
  classical
  let bs : Fin 1 → Val → Result := fun _ w => .jump 0 w
  change finish bs (.inr (0, v)) = _
  have path_eq (n : Nat) : path bs (.inr (0, v)) n = .inr (0, v) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [path, ih]; rfl
  have diverges : ¬ ∃ r, terminates bs (.inr (0, v)) r := by
    rintro ⟨r, i, hi⟩
    rw [path_eq] at hi
    cases hi
  rw [finish, dite_eq_right diverges, loopResult]

theorem default_uniformity_fails : ¬ Paper.Eqv [] before after [result] := by
  intro eq
  let env : Env := fun _ => .unit
  have fault : evalRegion after env = .fault := cfgRun_fault 1 _
  have observed := paper_same eq env (by simp [EnvTy, At])
  rw [fault] at observed
  change finish (fun (_ : Fin 1) v => .jump 0 v) (.inr (0, .inl .unit)) = .fault at observed
  rw [repeatDiverges] at observed
  cases observed

private theorem evalRepeat (A : Ty Empty) (env : Env) :
    evalRegion (SyntacticCategory.iterateRegion A (.br 0 (.inr (.var 0)) : Region Empty)) env =
      .diverges :=
  repeatDiverges (env 0)

theorem categorical_uniformity_fails :
    iterate sourceStep ≠ stateMap ≫ iterate targetStep := by
  rw [sourceStep, targetStep, iterateRepeat state, iterateRepeat result]
  let hp := SyntacticCategory.iterateRegion_valueBranches (repeatTag_typed state)
  let hq := SyntacticCategory.iterateRegion_valueBranches (repeatTag_typed result)
  let hr := Paper.RetainedLet.returnOnce_typed state_typed
  have hc : ValueBranches [state]
      (compLSubst (fun _ => Paper.RetainedLet.returnOnce changeState)
        (fun _ => SyntacticCategory.iterateRegion result (.br 0 (.inr (.var 0)))) 0) [result] :=
    hr.lsubst (fun i A hi =>
      LSubst.ValueFamily.liftVars (σ := fun _ => _) (Γ := [])
        (L := [result]) (K := [result])
        (fun _ _ hj => (List.mem_singleton.mp (List.mem_of_getElem? hj)).symm ▸ hq)
        state hi)
  change ofRegion hp ≠ ofRegion hr ≫ ofRegion hq
  rw [ofRegion_comp hr hq hc]
  intro eq
  let env : Env := fun _ => .inl .unit
  have henv : EnvTy [state] env := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .inl .unit
    | succ i => simp [At] at hi
  have e := paper_same ((ofRegion_eq_iff hp hc).mp eq) env henv
  change evalRegion (SyntacticCategory.iterateRegion state (.br 0 (.inr (.var 0)))) env = .fault at e
  rw [evalRepeat] at e
  cases e

theorem unit_eta_fails :
    ¬ Paper.Eqv [(Ty.unit : Ty Empty)] (.br 0 (.unit : Tm Empty)) (.br 0 (.var 0)) [Ty.unit] := by
  intro eq
  let env : Env := fun _ => .inl .unit
  have henv : EnvTy [(Ty.unit : Ty Empty)] env := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .alternateUnit rfl
    | succ i => simp [At] at hi
  have observed := paper_same eq env henv
  change Result.jump 0 .unit = Result.jump 0 (.inl .unit) at observed
  cases observed

private theorem projection_return_fails (i : Nat) (hi : i = 0 ∨ i = 1) :
    ¬ Paper.Eqv [(Ty.product Ty.unit Ty.unit : Ty Empty)]
      (.let₁ (.let₂ (.var 0) (.var i)) (.br 0 (.var 0)) : Region Empty)
      (.let₂ (.var 0) (.br 0 (.var i))) [Ty.unit] := by
  intro eq
  let env : Env := fun _ => .pair .unit .unit
  have henv : EnvTy [(Ty.product Ty.unit Ty.unit : Ty Empty)] env := by
    intro j A hj
    cases j with
    | zero => cases Option.some.inj hj; exact .pair .unit .unit
    | succ j => simp [At] at hj
  have obs := paper_same eq env henv
  rcases hi with rfl | rfl <;>
    change Result.fault = Result.jump 0 .unit at obs <;> cases obs

theorem fst_return_fails :
    ¬ Paper.Eqv [(Ty.product Ty.unit Ty.unit : Ty Empty)]
      (.let₁ (.let₂ (.var 0) (.var 1)) (.br 0 (.var 0)) : Region Empty)
      (.let₂ (.var 0) (.br 0 (.var 1))) [Ty.unit] :=
  projection_return_fails 1 (.inr rfl)

theorem snd_return_fails :
    ¬ Paper.Eqv [(Ty.product Ty.unit Ty.unit : Ty Empty)]
      (.let₁ (.let₂ (.var 0) (.var 0)) (.br 0 (.var 0)) : Region Empty)
      (.let₂ (.var 0) (.br 0 (.var 0))) [Ty.unit] :=
  projection_return_fails 0 (.inl rfl)


theorem mixed_swap_return_fails :
    let X : Ty Empty := Ty.unit
    let P := Ty.product X X
    ¬ Paper.Eqv [Ty.product P X]
      (.let₁ (.let₂ (.var 0) (.pair (.var 0) (.var 1))) (.br 0 (.var 0)) : Region Empty)
      (.let₂ (.var 0) (.br 0 (.pair (.var 0) (.var 1)))) [Ty.product X P] := by
  intro X P eq
  let env : Env := fun _ => .pair (.pair .unit .unit) .unit
  have henv : EnvTy [Ty.product P X] env := by
    intro j A hj
    cases j with
    | zero => cases Option.some.inj hj; exact .pair (.pair .unit .unit) .unit
    | succ j => simp [At] at hj
  have obs := paper_same eq env henv
  change Result.fault = Result.jump 0 (.pair .unit (.pair .unit .unit)) at obs
  cases obs

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction
