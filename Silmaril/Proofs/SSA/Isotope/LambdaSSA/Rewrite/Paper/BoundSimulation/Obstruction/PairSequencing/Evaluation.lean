module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Evaluation

/-! # Syntactic tests in the expression observer

The pair test faults on selected pairs if either operand starts with a unary let. The term-case
test faults at an expression case. The binary-let test marks a unary let in
its term body. A separate region test marks binary lets with computed
scrutinees. Each test is stable under constructor substitution.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Paper.BoundSimulation.Obstruction
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (UnitPayloadPolicy Env EnvTy Val ValTy Result ResultTy cfgRun
  cfgRun_typed)

universe u v

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

def startsLet : Tm Φ → Bool
  | .let₁ _ _ => true
  | _ => false

theorem startsLet_rename (t : Tm Φ) (ρ : Nat → Nat) :
    startsLet (t.rename ρ) = startsLet t := by
  cases t <;> rfl

theorem startsLet_subst (t : Tm Φ) (θ : Nat → Tm Φ)
    (hθ : ∀ i, startsLet (θ i) = false) :
    startsLet (t.subst θ) = startsLet t := by
  cases t with
  | var i => exact hθ i
  | _ => rfl

theorem startsLet_substOn {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α}
    (ht : Tm.HasType Γ t A) {θ : Nat → Tm Φ}
    (hθ : ∀ i A, At Γ i A → startsLet (θ i) = false) :
    startsLet (t.subst θ) = startsLet t := by
  cases ht with
  | var hi => exact hθ _ _ hi
  | _ => rfl

omit [HasTy Φ (Ty α)] in
theorem value_startsLet {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α}
    (ht : Tm.BranchValue Γ t A) : startsLet t = false := by cases ht <;> rfl

/-- Detect a computation under the value constructors of a scrutinee. -/
def computes : Tm Φ → Bool
  | .var _ | .unit => false
  | .pair a b => computes a || computes b
  | .inl a | .inr a => computes a
  | _ => true

theorem computes_rename (t : Tm Φ) (ρ : Nat → Nat) :
    computes (t.rename ρ) = computes t := by
  induction t <;> simp_all [Tm.rename, computes]

theorem computes_subst (t : Tm Φ) (θ : Nat → Tm Φ)
    (hθ : ∀ i, computes (θ i) = false) : computes (t.subst θ) = computes t := by
  induction t <;> simp_all [Tm.subst, computes]

theorem computes_substOn {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α}
    (ht : Tm.HasType Γ t A) {θ : Nat → Tm Φ}
    (hθ : ∀ i A, At Γ i A → computes (θ i) = false) :
    computes (t.subst θ) = computes t := by
  induction ht with
  | var hi => exact hθ _ _ hi
  | pair _ _ il ir => simp only [Tm.subst, computes, il hθ, ir hθ]
  | inl _ ih | inr _ ih => exact ih hθ
  | _ => rfl

omit [HasTy Φ (Ty α)] in
theorem value_not_computed {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α}
    (ht : Tm.BranchValue Γ t A) : computes t = false := by
  induction ht <;> simp_all [computes]

private theorem startsLet_of_not_computed {t : Tm Φ} (h : computes t = false) :
    startsLet t = false := by
  cases t <;> simp_all [computes, startsLet]

/-- Syntactic tests on expression and region evaluation. -/
structure TermObservation (Φ : Type v) {α : Type u} [HasTy Φ (Ty α)] where
  pairLet : Bool := false
  /-- Restrict the pair test to a selected primitive in the left operand. -/
  pairLetCall : Option (Φ → Bool) := none
  /-- Mark an expression-level binary let whose body starts with a unary let. -/
  binaryLetBody : Bool := false
  caseTerm : Bool := false
  /-- Mark term unary lets used as region scrutinees or as sum injection payloads. -/
  boundUnaryLet : Bool := false
  computedRegionLet₂ : Bool := false
  /-- Evaluate the argument before returning the selected call payload. -/
  evaluateCallOperand : Bool := false
  /-- Distinguish infinite local paths in tables with at least two rows. -/
  wideFeedback : Bool := false
  callResult : Φ → Option Val := fun _ => none
  callResult_typed (p : Φ) {v : Val} [UnitPayloadPolicy] :
    callResult p = some v → ValTy v (instrTrg p : Ty α) := by simp

def selectsPair (select : Option (Φ → Bool)) (a : Tm Φ) : Bool :=
  match select, a with
  | none, _ => true
  | some accepts, .op p _ => accepts p
  | some _, _ => false

theorem selectsPair_rename (select : Option (Φ → Bool)) (a : Tm Φ) (ρ : Nat → Nat) :
    selectsPair select (a.rename ρ) = selectsPair select a := by
  cases select <;> cases a <;> rfl

private theorem selectsPair_not_computed (accepts : Φ → Bool) {a : Tm Φ}
    (h : computes a = false) : selectsPair (some accepts) a = false := by
  cases a <;> first | rfl | cases h

theorem selectsPair_subst (select : Option (Φ → Bool)) (a : Tm Φ) (θ : Nat → Tm Φ)
    (hθ : ∀ i, computes (θ i) = false) :
    selectsPair select (a.subst θ) = selectsPair select a := by
  cases select with
  | none => rfl
  | some accepts =>
    cases a with
    | var i => exact selectsPair_not_computed accepts (hθ i)
    | _ => rfl

theorem selectsPair_substOn {Γ : VCtx (Ty α)} {a : Tm Φ} {A : Ty α}
    (ha : Tm.HasType Γ a A) (select : Option (Φ → Bool)) {θ : Nat → Tm Φ}
    (hθ : ∀ i D, At Γ i D → computes (θ i) = false) :
    selectsPair select (a.subst θ) = selectsPair select a := by
  cases select with
  | none => rfl
  | some accepts =>
    cases ha with
    | var hi => exact selectsPair_not_computed accepts (hθ _ _ hi)
    | _ => rfl

/-- Evaluate expressions with the selected tests and typed primitive results. -/
def evalTermWith (observation : TermObservation (α := α) Φ) : Tm Φ → Env → Option Val
  | .var i, env => some (env i)
  | .op p a, env =>
      if observation.evaluateCallOperand then
        evalTermWith observation a env >>= fun _ => observation.callResult p
      else if startsLet a then none else observation.callResult p
  | .let₁ x t, env => do
      let v ← evalTermWith observation x env
      evalTermWith observation t (extend env v)
  | .unit, _ => some .unit
  | .pair x y, env =>
      if observation.pairLet && selectsPair observation.pairLetCall x && (startsLet x || startsLet y) then none
      else do
        let v ← evalTermWith observation x env
        let w ← evalTermWith observation y env
        pure (.pair v w)
  | .let₂ x t, env =>
      if observation.binaryLetBody && startsLet t then none
      else do
        let .pair v w ← evalTermWith observation x env | none
        evalTermWith observation t (extend (extend env v) w)
  | .inl x, env =>
      if startsLet x && observation.boundUnaryLet then none
      else (evalTermWith observation x env).map Value.inl
  | .inr x, env =>
      if startsLet x && observation.boundUnaryLet then none
      else (evalTermWith observation x env).map Value.inr
  | .case x l r, env =>
      if observation.caseTerm then none else
        match evalTermWith observation x env with
        | some (.inl v) => evalTermWith observation l (extend env v)
        | some (.inr v) => evalTermWith observation r (extend env v)
        | _ => none
  | .abort _, _ => none

/-- A one-block iterator keeps the ordinary infinite-path outcome. -/
def markFeedback (observation : TermObservation (α := α) Φ) (n : Nat) : Bool :=
  if n < 2 then false else observation.wideFeedback

noncomputable def evalRegionWith (observation : TermObservation (α := α) Φ) : Region Φ → Env → Result
  | .br i t, env => match evalTermWith observation t env with
      | some v => .jump i v
      | none => .fault
  | .let₁ x r, env =>
      if startsLet x && observation.boundUnaryLet then .fault
      else match evalTermWith observation x env with
        | some v => evalRegionWith observation r (extend env v)
        | _ => .fault
  | .let₂ x r, env =>
      if observation.computedRegionLet₂ && computes x then .fault
      else match evalTermWith observation x env with
        | some (.pair v w) => evalRegionWith observation r (extend (extend env v) w)
        | _ => .fault
  | .case x l r, env => match evalTermWith observation x env with
      | some (.inl v) => evalRegionWith observation l (extend env v)
      | some (.inr v) => evalRegionWith observation r (extend env v)
      | _ => .fault
  | .cfg e n bs, env =>
      cfgRun n (fun i v => evalRegionWith observation (bs i) (extend env v))
        (evalRegionWith observation e env) (markFeedback observation n)

variable {observation : TermObservation (α := α) Φ}

local notation "evalTerm" => evalTermWith observation
local notation "evalRegion" => evalRegionWith observation

theorem evalTerm_rename (t : Tm Φ) {env env' : Env} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) : evalTerm (t.rename ρ) env' = evalTerm t env := by
  induction t generalizing env env' ρ with
  | var i => simp only [Tm.rename, evalTermWith, h]
  | op p a ih => simp only [Tm.rename, evalTermWith, startsLet_rename, ih h]
  | let₁ x t ix it =>
    simp only [Tm.rename, evalTermWith, ix h]
    cases evalTerm x env with
    | none => rfl
    | some v => exact it (extend_rename h v)
  | pair _ _ ix iy => simp only [Tm.rename, evalTermWith, startsLet_rename, selectsPair_rename, ix h, iy h]
  | unit => rfl
  | let₂ x t ix it =>
    simp only [Tm.rename, evalTermWith, startsLet_rename, ix h]
    split
    · rfl
    · cases evalTerm x env with
      | none => rfl
      | some v =>
        cases v <;> try rfl
        exact it (extend_rename (extend_rename h _) _)
  | inl _ ix => simp only [Tm.rename, evalTermWith, startsLet_rename, ix h]
  | inr _ ix => simp only [Tm.rename, evalTermWith, startsLet_rename, ix h]
  | case x l r ix il ir =>
    by_cases hm : observation.caseTerm
    · simp [Tm.rename, evalTermWith, hm]
    simp only [Tm.rename, evalTermWith, ix h, hm]
    cases evalTerm x env with
    | none => rfl
    | some v =>
      cases v <;> first | rfl | exact il (extend_rename h _) | exact ir (extend_rename h _)
  | abort _ _ => rfl

def RealizesWith (observation : TermObservation (α := α) Φ) (env env' : Env) (θ : Nat → Tm Φ) : Prop :=
  ∀ i, evalTermWith observation (θ i) env = some (env' i) ∧ computes (θ i) = false

local notation "Realizes" => RealizesWith observation

theorem RealizesWith.lift {env env' : Env} {θ : Nat → Tm Φ} (h : Realizes env env' θ) (v : Val) :
    Realizes (extend env v) (extend env' v) (Tm.liftSubst θ) := by
  intro i
  cases i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i =>
    change evalTerm ((θ i).rename Nat.succ) (extend env v) = some (env' i) ∧
      computes ((θ i).rename Nat.succ) = false
    rw [evalTerm_rename (θ i) (env := env) (env' := extend env v) (ρ := Nat.succ) (fun _ => rfl)]
    rw [computes_rename]
    exact h i

theorem evalTerm_subst (t : Tm Φ) {env env' : Env} {θ : Nat → Tm Φ}
    (h : Realizes env env' θ) : evalTerm (t.subst θ) env = evalTerm t env' := by
  induction t generalizing env env' θ with
  | var i => exact (h i).1
  | op p a ih =>
    simp only [Tm.subst, evalTermWith, ih h,
      startsLet_subst a θ (fun i => startsLet_of_not_computed (h i).2)]
  | let₁ x t ix it =>
    simp only [Tm.subst, evalTermWith, ix h]
    cases evalTerm x env' with
    | none => rfl
    | some v => exact it (h.lift v)
  | pair a b ix iy =>
    simp only [Tm.subst, evalTermWith, startsLet_subst a θ (fun i => startsLet_of_not_computed (h i).2),
      startsLet_subst b θ (fun i => startsLet_of_not_computed (h i).2),
      selectsPair_subst _ a θ (fun i => (h i).2), ix h, iy h]
  | unit => rfl
  | let₂ x t ix it =>
    have marker := startsLet_subst t (Tm.liftSubstN 2 θ)
      (fun i => startsLet_of_not_computed (((h.lift .unit).lift .unit) i).2)
    simp only [Tm.subst, evalTermWith, marker, ix h]
    split
    · rfl
    · cases evalTerm x env' with
      | none => rfl
      | some v =>
        cases v <;> try rfl
        exact it ((h.lift _).lift _)
  | inl t ix =>
    simp only [Tm.subst, evalTermWith, startsLet_subst t θ (fun i => startsLet_of_not_computed (h i).2), ix h]
  | inr t ix =>
    simp only [Tm.subst, evalTermWith, startsLet_subst t θ (fun i => startsLet_of_not_computed (h i).2), ix h]
  | case x l r ix il ir =>
    by_cases hm : observation.caseTerm
    · simp [Tm.subst, evalTermWith, hm]
    simp only [Tm.subst, evalTermWith, ix h, hm]
    cases evalTerm x env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift _) | exact ir (h.lift _)
  | abort _ _ => rfl

theorem evalRegion_subst (r : Region Φ) {env env' : Env} {θ : Nat → Tm Φ}
    (h : Realizes env env' θ) : evalRegion (r.substVars θ) env = evalRegion r env' := by
  induction r generalizing env env' θ with
  | br i t => simp only [substVars, evalRegionWith, evalTerm_subst t h]
  | let₁ x r ih =>
    simp only [substVars, evalRegionWith, evalTerm_subst x h,
      startsLet_subst x θ (fun i => startsLet_of_not_computed (h i).2)]
    split
    · rfl
    · cases evalTerm x env' with
      | none => rfl
      | some v => exact ih (h.lift v)
  | let₂ x r ih =>
    simp only [substVars, evalRegionWith, evalTerm_subst x h, computes_subst x θ (fun i => (h i).2)]
    split
    · rfl
    · cases evalTerm x env' with
      | none => rfl
      | some v =>
        cases v <;> try rfl
        exact ih ((h.lift _).lift _)
  | case x l r il ir =>
    simp only [substVars, evalRegionWith, evalTerm_subst x h]
    cases evalTerm x env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift _) | exact ir (h.lift _)
  | cfg e n bs ie ib =>
    simp only [substVars, evalRegionWith, ie h]
    congr 1
    funext i v
    exact ib i (h.lift v)

theorem evalRegion_renameVars (r : Region Φ) {env env' : Env} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) : evalRegion (r.renameVars ρ) env' = evalRegion r env := by
  rw [renameVars_eq_substVars]
  exact evalRegion_subst r (fun i => ⟨congrArg some (h i), rfl⟩)

theorem RealizesWith.single {env : Env} {t : Tm Φ} {v : Val} (h : evalTerm t env = some v)
    (ht : computes t = false) : Realizes env (extend env v) (Tm.singleSubst t) := by
  intro i
  cases i with
  | zero => exact ⟨h, ht⟩
  | succ i => exact ⟨rfl, rfl⟩

-- Replay the same observer with either unit payload policy.
set_option linter.concreteInstances false

variable [UnitPayloadPolicy]

theorem evalTerm_typed {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α}
    (ht : Tm.HasType Γ t A) {env : Env} (h : EnvTy Γ env) {v : Val}
    (he : evalTerm t env = some v) : ValTy v A := by
  induction ht generalizing env v with
  | var hi => cases Option.some.inj he; exact h hi
  | @op _ a p _ _ =>
    simp only [evalTermWith] at he
    split at he
    · cases ea : evalTerm a env with
      | none => simp [ea] at he
      | some value => exact observation.callResult_typed p (by simpa [ea] using he)
    · split at he
      · cases he
      · exact observation.callResult_typed p he
  | @let₁ _ a _ _ _ _ _ ia ib =>
    cases hx : evalTerm a env with
    | none => simp [evalTermWith, hx] at he
    | some x => exact ib (h.extend (ia h hx)) (by simpa [evalTermWith, hx] using he)
  | @pair _ a b _ _ _ _ ix iy =>
    by_cases guard : (observation.pairLet && selectsPair observation.pairLetCall a && (startsLet a || startsLet b)) = true
    · simp [evalTermWith, guard] at he
    · cases hx : evalTerm a env with
      | none => simp [evalTermWith, guard, hx] at he
      | some x =>
        cases hy : evalTerm b env with
        | none => simp [evalTermWith, guard, hx, hy] at he
        | some y =>
          simp [evalTermWith, guard, hx, hy] at he
          subst v
          exact .pair (ix h hx) (iy h hy)
  | unit => cases Option.some.inj he; exact .unit
  | @let₂ _ a b _ _ _ _ _ ix it =>
    by_cases guard : (observation.binaryLetBody && startsLet b) = true
    · simp [evalTermWith, guard] at he
    · cases hx : evalTerm a env with
      | none => simp [evalTermWith, guard, hx] at he
      | some x =>
        cases ix h hx with
        | pair ha hb => exact it ((h.extend ha).extend hb) (by simpa [evalTermWith, guard, hx] using he)
  | @inl _ a _ _ _ it =>
    by_cases marked : (startsLet a && observation.boundUnaryLet) = true
    · simp [evalTermWith, marked] at he
    · cases hx : evalTerm a env with
      | none => simp [evalTermWith, marked, hx] at he
      | some x =>
        simp [evalTermWith, marked, hx] at he
        subst v
        exact .inl (it h hx)
  | @inr _ a _ _ _ it =>
    by_cases marked : (startsLet a && observation.boundUnaryLet) = true
    · simp [evalTermWith, marked] at he
    · cases hx : evalTerm a env with
      | none => simp [evalTermWith, marked, hx] at he
      | some x =>
        simp [evalTermWith, marked, hx] at he
        subst v
        exact .inr (it h hx)
  | @case _ a _ _ _ _ _ _ _ _ ix il ir =>
    by_cases hm : observation.caseTerm
    · simp [evalTermWith, hm] at he
    cases hx : evalTerm a env with
    | none => simp [evalTermWith, hm, hx] at he
    | some x =>
      cases ix h hx with
      | inl hv => exact il (h.extend hv) (by simpa [evalTermWith, hm, hx] using he)
      | inr hv => exact ir (h.extend hv) (by simpa [evalTermWith, hm, hx] using he)
  | abort => cases he

theorem evalValue {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α}
    (ht : Tm.BranchValue Γ t A) {env : Env} (h : EnvTy Γ env) :
    ∃ v, evalTerm t env = some v ∧ ValTy v A := by
  induction ht with
  | var hi => exact ⟨_, rfl, h hi⟩
  | unit => exact ⟨_, rfl, .unit⟩
  | pair ha hb ix iy =>
    obtain ⟨x, hx, hxt⟩ := ix
    obtain ⟨y, hy, hyt⟩ := iy
    exact ⟨_, by simp [evalTermWith, value_startsLet ha, value_startsLet hb, hx, hy], .pair hxt hyt⟩
  | inl ht it =>
    obtain ⟨x, hx, hxt⟩ := it
    exact ⟨_, by simp [evalTermWith, value_startsLet ht, hx], .inl hxt⟩
  | inr ht it =>
    obtain ⟨x, hx, hxt⟩ := it
    exact ⟨_, by simp [evalTermWith, value_startsLet ht, hx], .inr hxt⟩

theorem evalRegion_typed {Γ : VCtx (Ty α)} {r : Region Φ} {L : LCtx (Ty α)}
    (hr : HasType Γ r L) {env : Env} (h : EnvTy Γ env) : ResultTy L (evalRegion r env) := by
  induction hr generalizing env with
  | br hi ht =>
    rw [evalRegionWith]
    split
    · exact ⟨_, hi, evalTerm_typed ht h (by assumption)⟩
    · trivial
  | let₁ ht _ ih =>
    rw [evalRegionWith]
    split
    · trivial
    · split
      · exact ih (h.extend (evalTerm_typed ht h (by assumption)))
      · trivial
  | let₂ ht _ ih =>
    rw [evalRegionWith]
    split
    · trivial
    · split
      · have hv := evalTerm_typed ht h (by assumption)
        cases hv with
        | pair ha hb => exact ih ((h.extend ha).extend hb)
      · trivial
  | case ht _ _ il ir =>
    rw [evalRegionWith]
    split
    · have hv := evalTerm_typed ht h (by assumption)
      cases hv with
      | inl ha => exact il (h.extend ha)
    · have hv := evalTerm_typed ht h (by assumption)
      cases hv with
      | inr hb => exact ir (h.extend hb)
    · trivial
  | cfg R _ _ ie ib =>
    rw [evalRegionWith]
    exact cfgRun_typed R _ (ie h) (fun i _ hv => ib i (h.extend hv))

def RealizesOnWith (observation : TermObservation (α := α) Φ) (Γ : VCtx (Ty α)) (env env' : Env) (θ : Nat → Tm Φ) : Prop :=
  ∀ i A, At Γ i A → evalTermWith observation (θ i) env = some (env' i) ∧ computes (θ i) = false

local notation "RealizesOn" => RealizesOnWith observation

omit [UnitPayloadPolicy] in
theorem RealizesOnWith.lift {Γ : VCtx (Ty α)} {env env' : Env} {θ : Nat → Tm Φ}
    (h : RealizesOn Γ env env' θ) (A : Ty α) (v : Val) :
    RealizesOn (A :: Γ) (extend env v) (extend env' v) (Tm.liftSubst θ) := by
  intro i B hi
  cases i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i =>
    change evalTerm ((θ i).rename Nat.succ) (extend env v) = some (env' i) ∧
      computes ((θ i).rename Nat.succ) = false
    rw [evalTerm_rename _ (env := env) (ρ := Nat.succ) (fun _ => rfl)]
    rw [computes_rename]
    exact h i B hi

omit [UnitPayloadPolicy] in
theorem evalTerm_substOn {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α}
    (ht : Tm.HasType Γ t A) {env env' : Env} {θ : Nat → Tm Φ}
    (h : RealizesOn Γ env env' θ) : evalTerm (t.subst θ) env = evalTerm t env' := by
  induction ht generalizing env env' θ with
  | var hi => exact (h _ _ hi).1
  | @op _ a p ha ih =>
    simp only [Tm.subst, evalTermWith, ih h,
      startsLet_substOn ha (fun i A hi => startsLet_of_not_computed (h i A hi).2)]
  | @let₁ _ a _ A _ _ _ ix it =>
    simp only [Tm.subst, evalTermWith, ix h]
    cases evalTerm a env' with
    | none => rfl
    | some v => exact it (h.lift A v)
  | @pair _ a b _ _ ha hb ix iy =>
    simp only [Tm.subst, evalTermWith, startsLet_substOn ha (fun i A hi => startsLet_of_not_computed (h i A hi).2),
      selectsPair_substOn ha _ (fun _ _ hi => (h _ _ hi).2), startsLet_substOn hb (fun i A hi => startsLet_of_not_computed (h i A hi).2), ix h, iy h]
  | unit => rfl
  | @let₂ _ a b A B _ _ hb ix it =>
    have marker := startsLet_substOn hb (θ := Tm.liftSubstN 2 θ)
      (fun i D hi => startsLet_of_not_computed (((h.lift A .unit).lift B .unit) i D hi).2)
    simp only [Tm.subst, evalTermWith, marker, ix h]
    split
    · rfl
    · cases evalTerm a env' with
      | none => rfl
      | some v =>
        cases v <;> try rfl
        exact it ((h.lift A _).lift B _)
  | inl ht it =>
    simp only [Tm.subst, evalTermWith,
      startsLet_substOn ht (fun i A hi => startsLet_of_not_computed (h i A hi).2), it h]
  | inr ht it =>
    simp only [Tm.subst, evalTermWith,
      startsLet_substOn ht (fun i A hi => startsLet_of_not_computed (h i A hi).2), it h]
  | @case _ a _ _ A B _ _ _ _ ix il ir =>
    by_cases hm : observation.caseTerm
    · simp [Tm.subst, evalTermWith, hm]
    simp only [Tm.subst, evalTermWith, ix h, hm]
    cases evalTerm a env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift A _) | exact ir (h.lift B _)
  | abort => rfl

omit [UnitPayloadPolicy] in
theorem evalRegion_substOn {Γ : VCtx (Ty α)} {r : Region Φ} {L : LCtx (Ty α)}
    (hr : HasType Γ r L) {env env' : Env} {θ : Nat → Tm Φ}
    (h : RealizesOn Γ env env' θ) : evalRegion (r.substVars θ) env = evalRegion r env' := by
  induction hr generalizing env env' θ with
  | br hi ht => simp only [substVars, evalRegionWith, evalTerm_substOn ht h]
  | @let₁ _ _ a _ A ht _ ih =>
    simp only [substVars, evalRegionWith, evalTerm_substOn ht h,
      startsLet_substOn ht (fun i A hi => startsLet_of_not_computed (h i A hi).2)]
    split
    · rfl
    · cases evalTerm a env' with
      | none => rfl
      | some v => exact ih (h.lift A v)
  | @let₂ _ _ a _ A B ht _ ih =>
    simp only [substVars, evalRegionWith, evalTerm_substOn ht h,
      computes_substOn ht (fun i A hi => (h i A hi).2)]
    split
    · rfl
    · cases evalTerm a env' with
      | none => rfl
      | some v =>
        cases v <;> try rfl
        exact ih ((h.lift A _).lift B _)
  | @case _ _ a _ _ A B ht _ _ il ir =>
    simp only [substVars, evalRegionWith, evalTerm_substOn ht h]
    cases evalTerm a env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift A _) | exact ir (h.lift B _)
  | cfg R _ _ ie ib =>
    simp only [substVars, evalRegionWith, ie h]
    congr 1
    funext i v
    exact ib i (h.lift (R i) v)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
