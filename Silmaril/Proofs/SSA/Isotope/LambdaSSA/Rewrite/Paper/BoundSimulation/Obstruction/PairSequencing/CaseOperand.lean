module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Soundness

/-! # The default observer with term cases marked in primitive arguments -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open BoundSimulation.Obstruction.Observer (Env EnvTy UnitPayloadPolicy Result)
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith evalTermWith evalRegionWith evalTerm_typed evalValue evalReturnRegion extension_same)

universe u
variable {Φ : Type u} [HasTy Φ (Ty Empty)]

local notation "U" => (Ty.unit : Ty Empty)

private theorem emptyEnv (env : Env) (policy : UnitPayloadPolicy) : @EnvTy policy Empty [] env :=
  fun _ _ h => by cases h

/-- Mark term cases and evaluate the argument before supplying a typed
left reply. The model assigns the same closed reply to each instruction. -/
private def caseObservation {reply : Tm Φ}
    (typed : ∀ (p : Φ), Tm.BranchValue [] (.inl reply) (instrTrg p : Ty Empty)) :
    TermObservation (α := Empty) Φ where
  caseTerm := true
  evaluateCallOperand := true
  callResult _ := evalTermWith {} (.inl reply) (fun _ => .unit)
  callResult_typed p _ _ h :=
    evalTerm_typed (observation := {}) (typed p).hasType (emptyEnv _ inferInstance) h

open scoped BoundSimulation.Obstruction.Observer.CanonicalUnit in
private theorem computed_step_same {obs : TermObservation (α := Empty) Φ}
    (evaluate : obs.evaluateCallOperand = true) {Γ L : List (Ty Empty)} {r s : Region Φ}
    (step : Paper.WithComputedCallReturns.Step Γ r s L) : SameWith obs Γ r s := by
  cases step with
  | @seq a p ha =>
    intro env he
    let inner : Tm.HasType (instrSrc p :: Γ) (.op p (.var 0)) (instrTrg p) := .op (.var rfl)
    rw [evalReturnRegion (.op ha) he, evalReturnRegion (.let₁ ha inner) he]
    simp only [evalTermWith, evaluate, ite_true]
    cases evalTermWith obs a env <;> rfl

open scoped BoundSimulation.Obstruction.Observer.CanonicalUnit in
theorem term_case_operand_ne {reply q v a b c : Tm Φ} {p : Φ} {l r s : Region Φ}
    {A B : Ty Empty} {L : List (Ty Empty)} {i : Nat}
    (reply_typed : ∀ (f : Φ), Tm.BranchValue [] (.inl reply) (instrTrg f : Ty Empty))
    (payload : Tm.BranchValue [] reply A) (query : Tm.BranchValue [U] q (instrSrc p))
    (ret : Tm.BranchValue [A, U] v B) :
    ¬ Paper.Extension.Eqv Paper.WithComputedCallReturns.Step [U] (.case (.op p (.case a b c)) l r)
      (.case (.op p q) (.br i v) s) L := by
  intro eq
  let obs := caseObservation reply_typed
  let env : Env := fun _ => .unit
  have he : EnvTy [U] env := by
    intro j X hj
    cases j with
    | zero => cases Option.some.inj hj; exact .unit
    | succ j => simp [At] at hj
  obtain ⟨x, ex, tx⟩ := evalValue (observation := {}) payload (emptyEnv (fun _ => .unit) inferInstance)
  obtain ⟨y, ey, _⟩ := evalValue (observation := obs) query he
  obtain ⟨z, ez, _⟩ := evalValue (observation := obs) ret (he.extend tx)
  have observed := extension_same (observation := obs) (computed_step_same rfl) eq env he
  have call : obs.callResult p = some (.inl x) := by
    simp only [obs, caseObservation, evalTermWith, Bool.and_false, Bool.false_eq_true, ite_false, ex, Option.map_some]
  simp only [evalRegionWith, evalTermWith, show obs.caseTerm = true from rfl,
    show obs.evaluateCallOperand = true from rfl, ite_true, ey, call] at observed
  change Result.fault =
    (match evalTermWith obs v (Semantics.extend env x) with
     | some value => Result.jump i value
     | none => .fault) at observed
  rw [ez] at observed
  cases observed

open scoped BoundSimulation.Obstruction.Observer.CanonicalUnit in
/-- An observer that marks term cases and gives every primitive no result
validates both exact call-site shapes. -/
theorem unit_case_return_ne_of_call_sites
    {Seed : VCtx (Ty Empty) → Region Φ → Region Φ → LCtx (Ty Empty) → Prop}
    (sites : ∀ {Γ L r s}, Seed Γ r s L →
      (∃ (p : Φ) (a b : Tm Φ) (k : Region Φ), r = .let₁ (.op p a) k ∧ s = .let₁ (.op p b) k) ∨
      (∃ (p : Φ) (a b : Tm Φ) (l k : Region Φ), r = .case (.op p a) l k ∧ s = .case (.op p b) l k)) :
    ¬ Paper.Extension.Eqv Seed [Ty.coprod Ty.unit Ty.unit]
      (.let₁ (.case (.var 0) .unit .unit) (.br 0 (.var 0)))
      (.case (.var 0) (.let₁ .unit (.br 0 (.var 0))) (.let₁ .unit (.br 0 (.var 0)))) [Ty.unit] := by
  intro eq
  let obs : TermObservation (α := Empty) Φ := { caseTerm := true }
  have step {Γ L r s} (h : Seed Γ r s L) : SameWith obs Γ r s := by
    intro env _
    rcases sites h with ⟨p, a, b, k, rfl, rfl⟩ | ⟨p, a, b, l, k, rfl, rfl⟩ <;>
      simp [evalRegionWith, evalTermWith, obs]
  let env : Env := Semantics.extend (fun _ => .unit) (.inl .unit)
  have valid : EnvTy [Ty.coprod U U] env := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .inl .unit
    | succ i => simp [At] at hi
  have observed := extension_same (observation := obs) step eq env valid
  change Result.fault = Result.jump 0 .unit at observed
  cases observed

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
