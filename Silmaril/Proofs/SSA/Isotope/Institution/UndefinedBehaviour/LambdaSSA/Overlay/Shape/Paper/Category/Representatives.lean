module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Defs
public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Values
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Literal
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.Raw.SSA.Isotope.LambdaSSA.ContinuationLaws

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay (nativeOutcomes extendModel Outcome mem_nativeOutcomes_iff)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Isotope.LambdaSSA.Region (ContinuationFamily liftLSubstVars)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper (Exit)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent
  (Runs literal continuation vars regionAt_iff)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops RegionAt PureValue)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (familyMember)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L K P : List (Ty κ)} {A : Ty κ}

abbrev ops {n : Nat} (M : Institution.Observational.Model.{u,w,x} Φ n) : Ops Φ M.α M.σ := ⟨M.instr, M.faults, M.prim⟩

private def eraseLabel {n : Nat} {α : Type w} {σ : Type x} : Outcome n α σ → Exit α σ
  | .ret i a s => .ret i.val a s
  | .fault s => .fault s
  | .diverge => .diverge

private theorem mem_runs (r : UB.Typed (Φ := Φ) Γ L) (M : Institution.Observational.Model.{u,w,x} Φ Γ.length) {env : Env M.α}
    (agree : Morphism.CaseSSA.EnvAgrees env M.bound) (s : M.σ) (o : Outcome L.length M.α M.σ) :
    o ∈ nativeOutcomes r M s ↔ Runs (ops M) env r.val s (eraseLabel o) := by
  cases o <;> exact mem_nativeOutcomes_iff r agree s _

/-- Change only the bound environment of the operational model. -/
abbrev rebind {n m : Nat} (M : Institution.Observational.Model.{u,w,x} Φ n) (bound : Fin m → Value M.α) :
    Institution.Observational.Model.{u,w,x} Φ m :=
  ⟨M.α, M.σ, M.instr, M.faults, M.prim, bound⟩

theorem outcomes_of_regionAt {Δ : List (Ty κ)} {n : Nat} (M : Institution.Observational.Model.{u,w,x} Φ n)
    (r : UB.Typed (Φ := Φ) Γ L) (t : UB.Typed (Φ := Φ) Δ L)
    {br : Fin Γ.length → Value M.α} {bt : Fin Δ.length → Value M.α} {env env' : Env M.α}
    (hbr : Morphism.CaseSSA.EnvAgrees env br) (hbt : Morphism.CaseSSA.EnvAgrees env' bt)
    (h : RegionAt (ops M) env r.val env' t.val) (s : M.σ) :
    nativeOutcomes r (rebind M br) s = nativeOutcomes t (rebind M bt) s := by
  apply Set.ext
  intro o
  exact (mem_runs r (rebind M br) hbr s o).trans ((regionAt_iff.mp h s _).trans (mem_runs t (rebind M bt) hbt s o).symm)

theorem branch_label_outcomes (M : Institution.Observational.Model.{u,w,x} Φ Γ.length)
    {env : Env M.α} (agree : Morphism.CaseSSA.EnvAgrees env M.bound)
    (i : Fin L.length) (label : At L i (L.get i))
    {t : Tm Φ} (ht : t.HasType Γ (L.get i)) {b : Value M.α}
    (pure : PureValue (ops M) env t b) (s : M.σ) :
    nativeOutcomes (⟨.br i t, .br label ht⟩ : UB.Typed (Φ := Φ) Γ L) M s =
      {Outcome.ret i b s} := by
  apply Set.ext
  intro o
  rw [mem_runs _ M agree, Set.mem_singleton_iff]
  cases o with
  | ret j c finish =>
    constructor
    · intro run
      have eval : Semantics.Region.Eval M.instr env (.br i t) s j c finish := run
      generalize eq : (j : Nat) = k at eval
      cases eval with
      | br arg =>
        obtain ⟨same, state⟩ := pure.unique arg
        exact Outcome.ret.injEq .. |>.mpr ⟨Fin.ext eq, same, state⟩
    · intro same
      obtain ⟨rfl, rfl, rfl⟩ := Outcome.ret.inj same
      exact Semantics.Region.Eval.br (pure.eval _)
  | fault t =>
    constructor
    · intro run
      cases run with | br arg => exact (pure.noFault arg).elim
    · intro eq
      cases eq
  | diverge =>
    constructor
    · intro run
      cases (show External.Diverges M.instr M.prim _ from run).unfold with
      | core step => cases step
      | br arg => exact (pure.noDiv arg).elim
    · intro eq
      cases eq

theorem branch_outcomes (M : Institution.Observational.Model.{u,w,x} Φ Γ.length)
    {env : Env M.α} (agree : Morphism.CaseSSA.EnvAgrees env M.bound)
    {t : Tm Φ} (ht : t.HasType Γ A) {b : Value M.α} (pure : PureValue (ops M) env t b) (s : M.σ) :
    nativeOutcomes (⟨.br 0 t, .br (ℓ := 0) rfl ht⟩ : UB.Typed (Φ := Φ) Γ [A]) M s =
      {Outcome.ret 0 b s} :=
  branch_label_outcomes M agree (L := [A]) 0 rfl ht pure s

theorem literal_outcomes {r : Region Φ} (hr : Region.ValueBranches Γ r L)
    {k : Nat → Region Φ} (hk : Region.LSubst.HasType Γ L K k)
    (M : Institution.Observational.Model.{u,w,x} Φ Γ.length) (s : M.σ) :
    nativeOutcomes ⟨r.lsubst k, hr.hasType.lsubst hk⟩ M s =
      Outcome.bind (nativeOutcomes ⟨r, hr.hasType⟩ M s)
        (fun j a t => nativeOutcomes ⟨k j, hk (List.getElem?_eq_getElem j.isLt)⟩ (extendModel M a) t) := by
  let env := envOfBound M.bound
  have agree : Morphism.CaseSSA.EnvAgrees env M.bound := envOfBound_agrees M.bound
  let source : UB.Typed (Φ := Φ) Γ L := ⟨r, hr.hasType⟩
  let next (j : Fin L.length) : UB.Typed (Φ := Φ) (L.get j :: Γ) K :=
    ⟨k j, hk (List.getElem?_eq_getElem j.isLt)⟩
  apply Set.ext
  intro o
  rw [mem_runs _ M agree, literal hr k s (eraseLabel o)]
  unfold Outcome.bind
  rw [Set.mem_ofPred_eq]
  have postRuns (i : Fin L.length) (a : Value M.α) (t : M.σ) :
      continuation (ops M) env k ⟨i.val, a, t⟩ (eraseLabel o) ↔
        o ∈ nativeOutcomes (next i) (extendModel M a) t :=
    (mem_runs (next i) (extendModel M a) (agree.extend a) t o).symm
  constructor
  · rintro ⟨e, first, post⟩
    cases e with
    | ret j a t =>
      let i : Fin L.length := ⟨j, hr.hasType.scoped.eval_label_lt first⟩
      exact .inr ⟨i, a, t, (mem_runs source M agree s (.ret i a t)).mpr first, (postRuns i a t).mp post⟩
    | fault t =>
      refine .inl ?_
      cases o with
      | ret | diverge => cases post
      | fault u =>
        have same : u = t := Exit.fault.inj post
        subst u
        exact (mem_runs source M agree s (.fault t)).mpr first
    | diverge =>
      refine .inl ?_
      cases o with
      | ret | fault => cases post
      | diverge => exact (mem_runs source M agree s .diverge).mpr first
  · rintro (early | ⟨i, a, t, first, next⟩)
    · cases o with
      | ret => exact early.elim
      | fault t => exact ⟨.fault t, (mem_runs source M agree s (.fault t)).mp early, rfl⟩
      | diverge => exact ⟨.diverge, (mem_runs source M agree s .diverge).mp early, rfl⟩
    · exact ⟨.ret i.val a t, (mem_runs source M agree s (.ret i a t)).mp first, (postRuns i a t).mpr next⟩

/-- Inserting a capture behind the newest variable does not change any
outcome of a block renamed around that capture. -/
theorem lift_outcomes {r : Region Φ} {A' : Ty κ} (source : r.HasType (A :: Γ) P)
    (M : Institution.Observational.Model.{u,w,x} Φ Γ.length) (old a : Value M.α) (s : M.σ)
    (typed : (r.renameVars (lift Nat.succ)).HasType (A :: A' :: Γ) P) :
    nativeOutcomes ⟨_, typed⟩ (extendModel (extendModel M old) a) s =
      nativeOutcomes ⟨r, source⟩ (extendModel M a) s := by
  let env := envOfBound M.bound
  have agree : Morphism.CaseSSA.EnvAgrees env M.bound := envOfBound_agrees M.bound
  apply Set.ext
  intro o
  rw [mem_runs _ _ ((agree.extend old).extend a), mem_runs _ _ (agree.extend a)]
  exact regionAt_iff.mp (vars (O := ops M) r (ρ := lift Nat.succ) (fun j => by cases j <;> rfl)) s _

/-- The actual family composition representative first produces the label and
payload, then runs the selected continuation at that exact final state. -/
theorem compose_outcomes (f : ContinuationFamily (Φ := Φ) Γ L K) (g : ContinuationFamily (Φ := Φ) Γ K P)
    (i : Fin L.length) (M : Institution.Observational.Model.{u,w,x} Φ Γ.length) (a : Value M.α) (s : M.σ) :
    nativeOutcomes (familyMember (f.compose g) i) (extendModel M a) s =
      Outcome.bind (nativeOutcomes (familyMember f i) (extendModel M a) s)
        (fun j b t => nativeOutcomes (familyMember g j) (extendModel M b) t) := by
  have hr := f.property (List.getElem?_eq_getElem (i := i.val) i.isLt)
  have hk : Region.LSubst.HasType Γ K P g.val := fun _ _ p => (g.property p).hasType
  have lifted := hk.liftVars (L.get i)
  change nativeOutcomes ⟨(f.val i).lsubst (liftLSubstVars g.val), hr.hasType.lsubst lifted⟩ _ _ = _
  rw [literal_outcomes hr lifted]
  congr 1
  funext j b t
  exact lift_outcomes (familyMember g j).property M a b t _

theorem identity_outcomes (i : Fin L.length) (M : Institution.Observational.Model.{u,w,x} Φ Γ.length) (a : Value M.α) (s : M.σ) :
    nativeOutcomes (familyMember (ContinuationFamily.identity (Φ := Φ) Γ L) i) (extendModel M a) s =
      {(.ret i a s : Outcome L.length M.α M.σ)} := by
  apply Set.ext
  intro o
  rw [mem_runs _ _ ((envOfBound_agrees M.bound).extend a), Set.mem_singleton_iff]
  constructor
  · intro run
    cases o with
    | ret j b t =>
      change Semantics.Region.Eval M.instr (extend (envOfBound M.bound) a)
        (.br i.val (.var 0)) s j.val b t at run
      generalize eq : j.val = label at run
      cases run with
      | br arg =>
        cases arg
        exact congrArg (fun j => Outcome.ret j a s) (Fin.ext eq)
    | fault => cases run with | br arg => cases arg
    | diverge =>
      cases (show External.Diverges M.instr M.prim _ from run).unfold with
      | br arg => cases arg
      | core step => cases step
  · rintro rfl
    exact Semantics.Region.Eval.br .var

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category
