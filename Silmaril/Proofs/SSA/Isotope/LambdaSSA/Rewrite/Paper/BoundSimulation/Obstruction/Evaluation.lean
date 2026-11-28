module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Trace
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! # Typed observations for the separation model

Term-level lets report a fault. Region-level lets still sequence their
scrutinee and body. Every constructor value evaluates successfully on a
typed environment, and successful jumps carry values at their label types.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction

abbrev Env := Nat → Val

/-- Observe a term with a distinguished fault at term-level lets. -/
def evalTerm : Tm Empty → Env → Option Val
  | .var i, env => some (env i)
  | .op p _, _ => p.elim
  | .let₁ _ _, _ => none
  | .unit, _ => some .unit
  | .pair x y, env => do
      let v ← evalTerm x env
      let w ← evalTerm y env
      pure (.pair v w)
  | .let₂ _ _, _ => none
  | .inl x, env => (evalTerm x env).map Value.inl
  | .inr x, env => (evalTerm x env).map Value.inr
  | .case x l r, env => match evalTerm x env with
      | some (.inl v) => evalTerm l (extend env v)
      | some (.inr v) => evalTerm r (extend env v)
      | _ => none
  | .abort _, _ => none

noncomputable def evalRegion : Region Empty → Env → Result
  | .br i t, env => match evalTerm t env with
      | some v => .jump i v
      | none => .fault
  | .let₁ x r, env => match evalTerm x env with
      | some v => evalRegion r (extend env v)
      | _ => .fault
  | .let₂ x r, env => match evalTerm x env with
      | some (.pair v w) => evalRegion r (extend (extend env v) w)
      | _ => .fault
  | .case x l r, env => match evalTerm x env with
      | some (.inl v) => evalRegion l (extend env v)
      | some (.inr v) => evalRegion r (extend env v)
      | _ => .fault
  | .cfg e n bs, env => cfgRun n (fun i v => evalRegion (bs i) (extend env v)) (evalRegion e env)

theorem evalTerm_rename (t : Tm Empty) {env env' : Env} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) : evalTerm (t.rename ρ) env' = evalTerm t env := by
  induction t generalizing env env' ρ with
  | var i => simp only [Tm.rename, evalTerm, h]
  | op p _ _ => exact p.elim
  | let₁ _ _ _ _ => rfl
  | pair _ _ ix iy => simp only [Tm.rename, evalTerm, ix h, iy h]
  | unit => rfl
  | let₂ => rfl
  | inl _ ix => simp only [Tm.rename, evalTerm, ix h]
  | inr _ ix => simp only [Tm.rename, evalTerm, ix h]
  | case x l r ix il ir =>
    simp only [Tm.rename, evalTerm, ix h]
    cases evalTerm x env with
    | none => rfl
    | some v =>
      cases v <;> first | rfl | exact il (extend_rename h _) | exact ir (extend_rename h _)
  | abort _ _ => rfl

def Realizes (env env' : Env) (θ : Nat → Tm Empty) : Prop :=
  ∀ i, evalTerm (θ i) env = some (env' i)

theorem Realizes.lift {env env' : Env} {θ : Nat → Tm Empty} (h : Realizes env env' θ) (v : Val) :
    Realizes (extend env v) (extend env' v) (Tm.liftSubst θ) := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
    change evalTerm ((θ i).rename Nat.succ) (extend env v) = some (env' i)
    rw [evalTerm_rename (θ i) (env := env) (env' := extend env v) (ρ := Nat.succ) (fun _ => rfl)]
    exact h i

theorem evalTerm_subst (t : Tm Empty) {env env' : Env} {θ : Nat → Tm Empty}
    (h : Realizes env env' θ) : evalTerm (t.subst θ) env = evalTerm t env' := by
  induction t generalizing env env' θ with
  | var i => exact h i
  | op p _ _ => exact p.elim
  | let₁ _ _ _ _ => rfl
  | pair _ _ ix iy => simp only [Tm.subst, evalTerm, ix h, iy h]
  | unit => rfl
  | let₂ => rfl
  | inl _ ix => simp only [Tm.subst, evalTerm, ix h]
  | inr _ ix => simp only [Tm.subst, evalTerm, ix h]
  | case x l r ix il ir =>
    simp only [Tm.subst, evalTerm, ix h]
    cases evalTerm x env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift _) | exact ir (h.lift _)
  | abort _ _ => rfl

theorem evalRegion_subst (r : Region Empty) {env env' : Env} {θ : Nat → Tm Empty}
    (h : Realizes env env' θ) : evalRegion (r.substVars θ) env = evalRegion r env' := by
  induction r generalizing env env' θ with
  | br i t => simp only [substVars, evalRegion, evalTerm_subst t h]
  | let₁ x r ih =>
    simp only [substVars, evalRegion, evalTerm_subst x h]
    cases evalTerm x env' with
    | none => rfl
    | some v => exact ih (h.lift v)
  | let₂ x r ih =>
    simp only [substVars, evalRegion, evalTerm_subst x h]
    cases evalTerm x env' with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      exact ih ((h.lift _).lift _)
  | case x l r il ir =>
    simp only [substVars, evalRegion, evalTerm_subst x h]
    cases evalTerm x env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift _) | exact ir (h.lift _)
  | cfg e n bs ie ib =>
    simp only [substVars, evalRegion, ie h]
    congr 1
    funext i v
    exact ib i (h.lift v)

theorem evalRegion_renameVars (r : Region Empty) {env env' : Env} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) : evalRegion (r.renameVars ρ) env' = evalRegion r env := by
  rw [renameVars_eq_substVars]
  exact evalRegion_subst r (fun i => congrArg some (h i))

theorem Realizes.single {env : Env} {t : Tm Empty} {v : Val} (h : evalTerm t env = some v) :
    Realizes env (extend env v) (Tm.singleSubst t) := by
  intro i
  cases i with
  | zero => exact h
  | succ i => rfl

/-- Select whether typed observations distinguish two possible unit payloads. -/
class UnitPayloadPolicy where
  allowAlternate : Bool

namespace AlternateUnit
scoped instance : UnitPayloadPolicy := ⟨true⟩
end AlternateUnit

namespace CanonicalUnit
scoped instance : UnitPayloadPolicy := ⟨false⟩
end CanonicalUnit

-- Each separating observer chooses its own scoped unit interpretation.
set_option linter.concreteInstances false

variable [policy : UnitPayloadPolicy]

universe u

variable {α : Type u}

inductive ValTy : Val → Ty α → Prop where
  /-- The observer gives each atomic sort one inhabitant. -/
  | base {a : α} : ValTy .unit (.base a)
  | unit : ValTy .unit .unit
  /-- An additional unit payload for tests of equations that would require unit canonicity. -/
  | alternateUnit (allowed : policy.allowAlternate = true) : ValTy (.inl .unit) .unit
  | pair {a b : Val} {A B : Ty α} :
      ValTy a A → ValTy b B → ValTy (.pair a b) (.product A B)
  | inl {a : Val} {A B : Ty α} : ValTy a A → ValTy (.inl a) (.coprod A B)
  | inr {b : Val} {A B : Ty α} : ValTy b B → ValTy (.inr b) (.coprod A B)

theorem ValTy.eq_unit {v : Val} (h : ValTy v (Ty.unit : Ty α)) (canonical : policy.allowAlternate = false) :
    v = .unit := by
  cases h with
  | unit => rfl
  | alternateUnit allowed => rw [canonical] at allowed; cases allowed

def EnvTy (Γ : VCtx (Ty α)) (env : Env) : Prop :=
  ∀ ⦃i A⦄, At Γ i A → ValTy (env i) A

theorem EnvTy.extend {Γ : VCtx (Ty α)} {A : Ty α} {env : Env} {v : Val}
    (h : EnvTy Γ env) (hv : ValTy v A) : EnvTy (A :: Γ) (extend env v) := by
  intro i D hi
  cases i with
  | zero => cases Option.some.inj hi; exact hv
  | succ i => exact h hi

theorem evalTerm_typed {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.HasType Γ t A) {env : Env} (h : EnvTy Γ env) {v : Val}
    (he : evalTerm t env = some v) : ValTy v A := by
  induction ht generalizing env v with
  | var hi => cases Option.some.inj he; exact h hi
  | @op _ _ f _ _ => exact f.elim
  | let₁ => cases he
  | @pair _ a b _ _ _ _ ix iy =>
    cases hx : evalTerm a env with
    | none => simp [evalTerm, hx] at he
    | some x =>
      cases hy : evalTerm b env with
      | none => simp [evalTerm, hx, hy] at he
      | some y =>
        simp [evalTerm, hx, hy] at he
        subst v
        exact .pair (ix h hx) (iy h hy)
  | unit => cases Option.some.inj he; exact .unit
  | let₂ => cases he
  | @inl _ a _ _ _ it =>
    cases hx : evalTerm a env with
    | none => simp [evalTerm, hx] at he
    | some x =>
      simp [evalTerm, hx] at he
      subst v
      exact .inl (it h hx)
  | @inr _ a _ _ _ it =>
    cases hx : evalTerm a env with
    | none => simp [evalTerm, hx] at he
    | some x =>
      simp [evalTerm, hx] at he
      subst v
      exact .inr (it h hx)
  | @case _ a _ _ _ _ _ _ _ _ ix il ir =>
    cases hx : evalTerm a env with
    | none => simp [evalTerm, hx] at he
    | some x =>
      cases ix h hx with
      | inl hv => exact il (h.extend hv) (by simpa [evalTerm, hx] using he)
      | inr hv => exact ir (h.extend hv) (by simpa [evalTerm, hx] using he)
  | abort => cases he

theorem evalValue {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue Γ t A) {env : Env} (h : EnvTy Γ env) :
    ∃ v, evalTerm t env = some v ∧ ValTy v A := by
  induction ht with
  | var hi => exact ⟨_, rfl, h hi⟩
  | unit => exact ⟨_, rfl, .unit⟩
  | pair _ _ ix iy =>
    obtain ⟨x, hx, hxt⟩ := ix
    obtain ⟨y, hy, hyt⟩ := iy
    exact ⟨_, by simp [evalTerm, hx, hy], .pair hxt hyt⟩
  | inl _ it =>
    obtain ⟨x, hx, hxt⟩ := it
    exact ⟨_, by simp [evalTerm, hx], .inl hxt⟩
  | inr _ it =>
    obtain ⟨x, hx, hxt⟩ := it
    exact ⟨_, by simp [evalTerm, hx], .inr hxt⟩

def ResultTy (L : LCtx (Ty α)) : Result → Prop
  | .jump i v => ∃ A, At L i A ∧ ValTy v A
  | .diverges => True
  | .fault => True

def FrameTy {n : Nat} (R : Fin n → Ty α) (L : LCtx (Ty α)) : Frame n → Prop
  | .inl r => ResultTy L r
  | .inr (i, v) => ValTy v (R i)

theorem enter_typed {n : Nat} (R : Fin n → Ty α) {L : LCtx (Ty α)} {r : Result}
    (h : ResultTy (List.ofFn R ++ L) r) : FrameTy R L (enter n r) := by
  cases r with
  | jump i v =>
    obtain ⟨A, hi, hv⟩ := h
    by_cases hlt : i < n
    · rw [enter, dite_eq_left hlt]
      change ValTy v (R ⟨i, hlt⟩)
      have he : i < (List.ofFn R).length := by simpa only [List.length_ofFn] using hlt
      have hR : At (List.ofFn R) i (R ⟨i, hlt⟩) := by simp [At, List.getElem?_eq_getElem he]
      rw [At, List.getElem?_append_left he] at hi
      cases Option.some.inj (hi.symm.trans hR)
      exact hv
    · rw [enter, dite_eq_right hlt]
      have he : (List.ofFn R).length ≤ i := by
        simpa only [List.length_ofFn] using Nat.le_of_not_gt hlt
      rw [At, List.getElem?_append_right he, List.length_ofFn] at hi
      exact ⟨A, hi, hv⟩
  | diverges => trivial
  | fault => trivial

theorem step_typed {n : Nat} (R : Fin n → Ty α) (L : LCtx (Ty α))
    {bs : Fin n → Val → Result} (hbs : ∀ i v, ValTy v (R i) → ResultTy (List.ofFn R ++ L) (bs i v))
    (s : Frame n) (hs : FrameTy R L s) : FrameTy R L (step bs s) := by
  cases s with
  | inl r => exact hs
  | inr s =>
    obtain ⟨i, v⟩ := s
    exact enter_typed R (hbs i v hs)

theorem cfgRun_typed {n : Nat} {mark : Bool} (R : Fin n → Ty α) (L : LCtx (Ty α))
    {bs : Fin n → Val → Result} {r : Result}
    (he : ResultTy (List.ofFn R ++ L) r)
    (hb : ∀ i v, ValTy v (R i) → ResultTy (List.ofFn R ++ L) (bs i v)) :
    ResultTy L (cfgRun n bs r mark) := by
  classical
  have good (i : Nat) : FrameTy R L (path bs (enter n r) i) := by
    induction i with
    | zero => exact enter_typed R he
    | succ i ih => exact step_typed R L hb _ ih
  by_cases hex : ∃ r', terminates bs (enter n r) r'
  · obtain ⟨r', i, hi⟩ := hex
    have h := good i
    rw [hi] at h
    change ResultTy L (finish bs (enter n r) mark)
    rw [finish_of_terminal bs _ hi]
    exact h
  · change ResultTy L (finish bs (enter n r) mark)
    rw [finish, dite_eq_right hex]
    cases mark <;> trivial

theorem evalRegion_typed {Γ : VCtx (Ty Empty)} {r : Region Empty} {L : LCtx (Ty Empty)}
    (hr : HasType Γ r L) {env : Env} (h : EnvTy Γ env) : ResultTy L (evalRegion r env) := by
  induction hr generalizing env with
  | br hi ht =>
    rw [evalRegion]
    split
    · exact ⟨_, hi, evalTerm_typed ht h (by assumption)⟩
    · trivial
  | let₁ ht _ ih =>
    rw [evalRegion]
    split
    · exact ih (h.extend (evalTerm_typed ht h (by assumption)))
    · trivial
  | let₂ ht _ ih =>
    rw [evalRegion]
    split
    · have hv := evalTerm_typed ht h (by assumption)
      cases hv with
      | pair ha hb => exact ih ((h.extend ha).extend hb)
    · trivial
  | case ht _ _ il ir =>
    rw [evalRegion]
    split
    · have hv := evalTerm_typed ht h (by assumption)
      cases hv with
      | inl ha => exact il (h.extend ha)
    · have hv := evalTerm_typed ht h (by assumption)
      cases hv with
      | inr hb => exact ir (h.extend hb)
    · trivial
  | cfg R _ _ ie ib =>
    rw [evalRegion]
    exact cfgRun_typed R _ (ie h) (fun i _ hv => ib i (h.extend hv))

omit [UnitPayloadPolicy] in
theorem mapTerminal_id {n : Nat} (s : Frame n) : mapTerminal id s = s := by cases s <;> rfl

theorem cfgRun_congr {n : Nat} {mark : Bool} (R : Fin n → Ty α) (L : LCtx (Ty α))
    {bs bs' : Fin n → Val → Result} {r : Result}
    (he : ResultTy (List.ofFn R ++ L) r)
    (typed : ∀ i v, ValTy v (R i) → ResultTy (List.ofFn R ++ L) (bs i v))
    (hb : ∀ i v, ValTy v (R i) → bs i v = bs' i v) :
    cfgRun n bs r mark = cfgRun n bs' r mark := by
  have comm (s : Frame n) (hs : FrameTy R L s) : step bs' s = step bs s := by
    cases s with
    | inl _ => rfl
    | inr s =>
      obtain ⟨i, v⟩ := s
      change enter n (bs' i v) = enter n (bs i v)
      rw [hb i v hs]
  have hh := finish_mapTerminalOn (mark := mark) bs bs' id rfl (FrameTy R L)
    (step_typed R L typed) (fun s hs => by simp only [mapTerminal_id]; exact comm s hs)
    (enter n r) (enter_typed R he)
  simpa only [mapTerminal_id, id_eq, cfgRun] using hh.symm

def RealizesOn (Γ : VCtx (Ty Empty)) (env env' : Env) (θ : Nat → Tm Empty) : Prop :=
  ∀ i A, At Γ i A → evalTerm (θ i) env = some (env' i)

omit [UnitPayloadPolicy] in
theorem RealizesOn.lift {Γ : VCtx (Ty Empty)} {env env' : Env} {θ : Nat → Tm Empty}
    (h : RealizesOn Γ env env' θ) (A : Ty Empty) (v : Val) :
    RealizesOn (A :: Γ) (extend env v) (extend env' v) (Tm.liftSubst θ) := by
  intro i B hi
  cases i with
  | zero => rfl
  | succ i =>
    change evalTerm ((θ i).rename Nat.succ) (extend env v) = some (env' i)
    rw [evalTerm_rename _ (env := env) (ρ := Nat.succ) (fun _ => rfl)]
    exact h i B hi

omit [UnitPayloadPolicy] in
theorem evalTerm_substOn {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.HasType Γ t A) {env env' : Env} {θ : Nat → Tm Empty}
    (h : RealizesOn Γ env env' θ) : evalTerm (t.subst θ) env = evalTerm t env' := by
  induction ht generalizing env env' θ with
  | var hi => exact h _ _ hi
  | @op _ _ f _ _ => exact f.elim
  | let₁ => rfl
  | pair _ _ ix iy => simp only [Tm.subst, evalTerm, ix h, iy h]
  | unit => rfl
  | let₂ => rfl
  | inl _ it => simp only [Tm.subst, evalTerm, it h]
  | inr _ it => simp only [Tm.subst, evalTerm, it h]
  | @case _ a _ _ A B _ _ _ _ ix il ir =>
    simp only [Tm.subst, evalTerm, ix h]
    cases evalTerm a env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift A _) | exact ir (h.lift B _)
  | abort => rfl

omit [UnitPayloadPolicy] in
theorem evalRegion_substOn {Γ : VCtx (Ty Empty)} {r : Region Empty} {L : LCtx (Ty Empty)}
    (hr : HasType Γ r L) {env env' : Env} {θ : Nat → Tm Empty}
    (h : RealizesOn Γ env env' θ) : evalRegion (r.substVars θ) env = evalRegion r env' := by
  induction hr generalizing env env' θ with
  | br hi ht => simp only [substVars, evalRegion, evalTerm_substOn ht h]
  | @let₁ _ _ a _ A ht _ ih =>
    simp only [substVars, evalRegion, evalTerm_substOn ht h]
    cases evalTerm a env' with
    | none => rfl
    | some v => exact ih (h.lift A v)
  | @let₂ _ _ a _ A B ht _ ih =>
    simp only [substVars, evalRegion, evalTerm_substOn ht h]
    cases evalTerm a env' with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      exact ih ((h.lift A _).lift B _)
  | @case _ _ a _ _ A B ht _ _ il ir =>
    simp only [substVars, evalRegion, evalTerm_substOn ht h]
    cases evalTerm a env' with
    | none => rfl
    | some v => cases v <;> first | rfl | exact il (h.lift A _) | exact ir (h.lift B _)
  | cfg R _ _ ie ib =>
    simp only [substVars, evalRegion, ie h]
    congr 1
    funext i v
    exact ib i (h.lift (R i) v)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
