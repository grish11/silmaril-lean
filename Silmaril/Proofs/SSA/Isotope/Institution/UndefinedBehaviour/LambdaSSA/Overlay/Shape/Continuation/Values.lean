module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

universe u v w x

variable {Φ : Type u} {α : Type w} {σ : Type x}

/-- A substituted constructor term must return a fixed value, with no state
change, fault, or divergent evaluation. -/
structure PureValue (O : Ops Φ α σ) (env : Env α) (a : Tm Φ) (v : Value α) : Prop where
  eval : ∀ s, Semantics.Tm.Eval O.instr env a s v s
  unique : ∀ {s u t}, Semantics.Tm.Eval O.instr env a s u t → u = v ∧ t = s
  noFault : ∀ {s t}, ¬ Semantics.Tm.Fault O.instr O.faults env a s t
  noDiv : ∀ {s}, ¬ Semantics.Tm.ExternalDiverges O.instr O.prim env a s

namespace PureValue

variable {O : Ops Φ α σ} {env env' : Env α} {a b : Tm Φ} {v u : Value α}

theorem same (h : PureValue O env a v) (k : PureValue O env' b v) :
    TermAt O env a env' b where
  eval := ⟨fun h' => by obtain ⟨rfl, rfl⟩ := h.unique h'; exact k.eval _,
    fun k' => by obtain ⟨rfl, rfl⟩ := k.unique k'; exact h.eval _⟩
  fault := ⟨fun h' => (h.noFault h').elim, fun k' => (k.noFault k').elim⟩
  div := ⟨fun h' => (h.noDiv h').elim, fun k' => (k.noDiv k').elim⟩

theorem var (i : Nat) : PureValue O env (.var i) (env i) where
  eval _ := .var
  unique := by intro s u t h; cases h; exact ⟨rfl, rfl⟩
  noFault := by intro s t h; cases h
  noDiv := by intro s h; cases h

theorem unit : PureValue O env (.unit : Tm Φ) .unit where
  eval _ := .unit
  unique := by intro s u t h; cases h; exact ⟨rfl, rfl⟩
  noFault := by intro s t h; cases h
  noDiv := by intro s h; cases h

theorem pair (h : PureValue O env a v) (k : PureValue O env b u) :
    PureValue O env (.pair a b) (.pair v u) where
  eval s := .pair (h.eval s) (k.eval s)
  unique := by
    intro s u t run
    cases run with
    | pair left right =>
      obtain ⟨rfl, rfl⟩ := h.unique left
      obtain ⟨rfl, rfl⟩ := k.unique right
      exact ⟨rfl, rfl⟩
  noFault := by
    intro s t run
    cases run with
    | pair_left left => exact h.noFault left
    | pair_right _ right => exact k.noFault right
  noDiv := by
    intro s run
    cases run with
    | pair_left left => exact h.noDiv left
    | pair_right _ right => exact k.noDiv right

theorem inl (h : PureValue O env a v) : PureValue O env (.inl a) (.inl v) where
  eval s := .inl (h.eval s)
  unique := by
    intro s u t run
    cases run with
    | inl run => obtain ⟨rfl, rfl⟩ := h.unique run; exact ⟨rfl, rfl⟩
  noFault := by intro s t run; cases run with | inl arg => exact h.noFault arg
  noDiv := by intro s run; cases run with | inl arg => exact h.noDiv arg

theorem inr (h : PureValue O env a v) : PureValue O env (.inr a) (.inr v) where
  eval s := .inr (h.eval s)
  unique := by
    intro s u t run
    cases run with
    | inr run => obtain ⟨rfl, rfl⟩ := h.unique run; exact ⟨rfl, rfl⟩
  noFault := by intro s t run; cases run with | inr arg => exact h.noFault arg
  noDiv := by intro s run; cases run with | inr arg => exact h.noDiv arg

theorem weaken (h : PureValue O env a v) (u : Value α) :
    PureValue O (extend env u) (a.rename Nat.succ) v where
  eval s := (h.eval s).rename (fun _ => rfl)
  unique run := h.unique (Semantics.Tm.Eval.of_rename (ρ := Nat.succ) (fun _ => rfl) run)
  noFault run := h.noFault (Semantics.Tm.Fault.of_rename (ρ := Nat.succ) (fun _ => rfl) run)
  noDiv run := h.noDiv (Semantics.Tm.ExternalDiverges.of_rename (ρ := Nat.succ) (fun _ => rfl) run)

theorem ofBranchValue {τ : Type v} [TypeFormers τ] {Γ : VCtx τ} {A : τ}
    (h : a.BranchValue Γ A) : ∃ v, PureValue O env a v := by
  induction h with
  | var => exact ⟨_, .var _⟩
  | unit => exact ⟨_, .unit⟩
  | pair _ _ left right =>
    obtain ⟨_, hv⟩ := left
    obtain ⟨_, hu⟩ := right
    exact ⟨_, hv.pair hu⟩
  | inl _ ih => obtain ⟨_, hv⟩ := ih; exact ⟨_, hv.inl⟩
  | inr _ ih => obtain ⟨_, hv⟩ := ih; exact ⟨_, hv.inr⟩

end PureValue

section Case

variable {O : Ops Φ α σ} {env : Env α}
  {a : Tm Φ} {l r : LambdaSSA.Region Φ} {v : Value α}

theorem case_pure_inl (h : PureValue O env a (.inl v)) :
    RegionAt O env (.case a l r) (extend env v) l where
  eval := by
    intro s i out t
    constructor
    · intro run; cases run with
      | case_inl head body =>
        obtain ⟨same, rfl⟩ := h.unique head
        cases same; exact body
      | case_inr head _ => cases (h.unique head).1
    · exact fun run => .case_inl (h.eval _) run
  fault := by
    intro s t
    constructor
    · intro run; cases run with
      | case_arg head => exact (h.noFault head).elim
      | case_inl head body =>
        obtain ⟨same, rfl⟩ := h.unique head
        cases same; exact body
      | case_inr head _ => cases (h.unique head).1
    · exact fun run => .case_inl (h.eval _) run
  div := by
    intro s
    constructor
    · intro run; cases run.unfold with
      | case_arg head => exact (h.noDiv head).elim
      | core step => cases step with
        | case_inl head body =>
          obtain ⟨same, rfl⟩ := h.unique head
          cases same; exact body
        | case_inr head _ => cases (h.unique head).1
    · exact fun run => .fold_core (.case_inl (h.eval _) run)

theorem case_pure_inr (h : PureValue O env a (.inr v)) :
    RegionAt O env (.case a l r) (extend env v) r where
  eval := by
    intro s i out t
    constructor
    · intro run; cases run with
      | case_inl head _ => cases (h.unique head).1
      | case_inr head body =>
        obtain ⟨same, rfl⟩ := h.unique head
        cases same; exact body
    · exact fun run => .case_inr (h.eval _) run
  fault := by
    intro s t
    constructor
    · intro run; cases run with
      | case_arg head => exact (h.noFault head).elim
      | case_inl head _ => cases (h.unique head).1
      | case_inr head body =>
        obtain ⟨same, rfl⟩ := h.unique head
        cases same; exact body
    · exact fun run => .case_inr (h.eval _) run
  div := by
    intro s
    constructor
    · intro run; cases run.unfold with
      | case_arg head => exact (h.noDiv head).elim
      | core step => cases step with
        | case_inl head _ => cases (h.unique head).1
        | case_inr head body =>
          obtain ⟨same, rfl⟩ := h.unique head
          cases same; exact body
    · exact fun run => .fold_core (.case_inr (h.eval _) run)

end Case


@[expose] def Realizes (O : Ops Φ α σ) (env : Env α) (θ : Nat → Tm Φ) (source : Env α) : Prop :=
  ∀ i, PureValue O env (θ i) (source i)

namespace Realizes

variable {O : Ops Φ α σ} {env source : Env α} {θ : Nat → Tm Φ}

theorem lift (h : Realizes O env θ source) (v : Value α) :
    Realizes O (extend env v) (Tm.liftSubst θ) (extend source v) := by
  intro i
  cases i with
  | zero => exact .var 0
  | succ i => exact (h i).weaken v

theorem single {a : Tm Φ} {v : Value α} (h : PureValue O env a v) :
    Realizes O env (Tm.singleSubst a) (extend env v) := by
  intro i
  cases i with
  | zero => exact h
  | succ i => exact .var i

theorem replace (env : Env α) (v : Value α) :
    Realizes O (extend env v) (Tm.replaceNewest (.inl (.var 0))) (extend env (.inl v)) ∧
      Realizes O (extend env v) (Tm.replaceNewest (.inr (.var 0))) (extend env (.inr v)) := by
  constructor
  · intro i
    cases i with
    | zero => exact (PureValue.var 0).inl
    | succ i => exact .var (i + 1)
  · intro i
    cases i with
    | zero => exact (PureValue.var 0).inr
    | succ i => exact .var (i + 1)

end Realizes

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation
