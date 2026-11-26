module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category (returnPayload splitPayload)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)

universe u x

variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)] {σ : Type x} {Γ : List (Silmaril.Ty Empty)}
variable {A B : Silmaril.Ty Empty}
variable (prim : StatePrimitives Φ σ) (env : Bindings Γ)

private abbrev initialEnv : Env Unit := envOfBound (model prim env).raw.bound

private theorem instr_deterministic : InstrDeterministic (model prim env).raw.instr := by
  intro f a s b t c u first second
  obtain ⟨ha, first⟩ := first
  obtain ⟨_, second⟩ := second
  cases reply : prim f ⟨a, ha⟩ s with
  | ret v s' =>
    rw [reply] at first second
    exact ⟨first.1.symm.trans second.1, first.2.symm.trans second.2⟩
  | fault | diverge => rw [reply] at first; exact first.elim

private theorem expr_eval (a : Expr Γ A) (s : σ) :
    Tm.Eval (model prim env).raw.instr (initialEnv prim env) a.term s (a.eval env).val s := by
  induction a with
  | var i =>
    change Tm.Eval _ _ (.var i) s ((model prim env).raw.bound i) s
    rw [← envOfBound_agrees (model prim env).raw.bound i]
    exact .var
  | unit => exact .unit
  | pair _ _ left right => exact .pair left right
  | inl _ eval => exact .inl eval
  | inr _ eval => exact .inr eval

private theorem expr_no_fault (a : Expr Γ A) {s t : σ} :
    ¬ Tm.Fault (model prim env).raw.instr (model prim env).raw.faults (initialEnv prim env) a.term s t := by
  induction a generalizing s t <;> intro fault
  case var => cases fault
  case unit => cases fault
  case pair a b left right =>
    cases fault with
    | pair_left arg => exact left arg
    | pair_right _ arg => exact right arg
  case inl a ih => cases fault with | inl arg => exact ih arg
  case inr a ih => cases fault with | inr arg => exact ih arg

private theorem expr_no_diverge (a : Expr Γ A) {s : σ} :
    ¬ Tm.ExternalDiverges (model prim env).raw.instr (model prim env).raw.prim
      (initialEnv prim env) a.term s := by
  induction a generalizing s <;> intro div
  case var => cases div
  case unit => cases div
  case pair a b left right =>
    cases div with
    | pair_left arg => exact left arg
    | pair_right _ arg => exact right arg
  case inl a ih => cases div with | inl arg => exact ih arg
  case inr a ih => cases div with | inr arg => exact ih arg

private theorem exact_return {L : List (Silmaril.Ty Empty)} (r : LambdaSSA.UB.Typed (Φ := Φ) Γ L)
    (s t : σ) (i : Fin L.length) (b : Value Unit)
    (run : Region.Eval (model prim env).raw.instr (initialEnv prim env) r.val s i b t)
    (noFault : ∀ t, ¬ Region.Fault (model prim env).raw.instr (model prim env).raw.faults
      (initialEnv prim env) r.val s t)
    (noDiv : ¬ External.Diverges (model prim env).raw.instr (model prim env).raw.prim
      (.region (initialEnv prim env) r.val s)) :
    nativeOutcomes r (model prim env).raw s = {Outcome.ret i b t} := by
  ext o
  rw [mem_nativeOutcomes_iff r (envOfBound_agrees (model prim env).raw.bound), Set.mem_singleton_iff]
  cases o with
  | ret j c u =>
    constructor
    · intro evaluated
      obtain ⟨label, value, final⟩ := evaluated.deterministic (instr_deterministic prim env) run
      exact Outcome.ret.injEq .. |>.mpr ⟨Fin.ext label, value, final⟩
    · intro eq
      obtain ⟨rfl, rfl, rfl⟩ := Outcome.ret.inj eq
      exact run
  | fault t => exact ⟨fun h => (noFault t h).elim, fun h => by cases h⟩
  | diverge => exact ⟨fun h => (noDiv h).elim, fun h => by cases h⟩

theorem observe_branch {L : List (Silmaril.Ty Empty)} (i : Fin L.length)
    (a : Expr Γ (L.get i)) (s : σ) :
    denote (.native ⟨.br i a.term, .br (List.getElem?_eq_getElem i.isLt) a.typed⟩)
      (model prim env).raw s = WithTop.some {Outcome.ret i (a.eval env).val s} := by
  apply congrArg WithTop.some
  apply exact_return prim env _ s s i _ (.br (expr_eval prim env a s))
  · intro t h
    cases h with | br arg => exact expr_no_fault prim env a arg
  · intro h
    cases h.unfold with
    | br arg => exact expr_no_diverge prim env a arg
    | core step => cases step

theorem observe_return (a : Expr Γ A) (s : σ) :
    denote (.native (Program.returnRegion (Φ := Φ) a)) (model prim env).raw s =
      returnPayload (a.eval env).val s :=
  observe_branch prim env (0 : Fin [A].length) a s

private theorem branch_var_no_div {e : Env Unit} {i : Nat} {s : σ} :
    ¬ External.Diverges (model prim env).raw.instr (model prim env).raw.prim (.region e (.br i (.var 0)) s) := by
  intro h
  cases h.unfold with
  | br arg => cases arg
  | core step => cases step

theorem observe_case (a : Expr Γ (.coprod A B)) (s : σ) :
    denote (.native (Program.caseRegion (Φ := Φ) a)) (model prim env).raw s =
      (match splitPayload (a.eval env) with
      | .inl b => WithTop.some {Outcome.ret (0 : Fin 2) b.val s}
      | .inr b => WithTop.some {Outcome.ret (1 : Fin 2) b.val s}) := by
  have noFault (t : σ) :
      ¬ Region.Fault (model prim env).raw.instr (model prim env).raw.faults
        (initialEnv prim env) (Program.caseRegion a).val s t := by
    intro h
    cases h with
    | case_arg head => exact expr_no_fault prim env a head
    | case_inl _ body | case_inr _ body => cases body with | br head => cases head
  have noDiv : ¬ External.Diverges (model prim env).raw.instr (model prim env).raw.prim
      (.region (initialEnv prim env) (Program.caseRegion a).val s) := by
    intro h
    cases h.unfold with
    | case_arg head => exact expr_no_diverge prim env a head
    | core step =>
      cases step with
      | case_inl _ tail | case_inr _ tail => exact (branch_var_no_div prim env tail).elim
  have run := expr_eval prim env a s
  generalize a.eval env = result at run ⊢
  obtain ⟨value, typed⟩ := result
  cases typed with
  | inl typed =>
    exact congrArg WithTop.some (exact_return prim env (Program.caseRegion a) s s (0 : Fin 2) _
      (.case_inl run (.br .var)) noFault noDiv)
  | inr typed =>
    exact congrArg WithTop.some (exact_return prim env (Program.caseRegion a) s s (1 : Fin 2) _
      (.case_inr run (.br .var)) noFault noDiv)

private theorem request_eval_iff (f : Φ) (arg : Expr Γ (instrSrc f)) (s t : σ) (v : Value Unit) :
    Region.Eval (model prim env).raw.instr (initialEnv prim env) (Program.requestRegion f arg).val s 0 v t ↔
      (prim f (arg.eval env) s).returns v t := by
  constructor
  · intro run
    cases run with
    | br term =>
      cases term with
      | op head instruction =>
        obtain ⟨rfl, rfl⟩ := head.deterministic (instr_deterministic prim env) (expr_eval prim env arg s)
        obtain ⟨_, reply⟩ := instruction
        exact reply
  · intro reply
    exact .br (.op (expr_eval prim env arg s) ⟨(arg.eval env).property, reply⟩)

private theorem request_fault_iff (f : Φ) (arg : Expr Γ (instrSrc f)) (s t : σ) :
    Region.Fault (model prim env).raw.instr (model prim env).raw.faults
      (initialEnv prim env) (Program.requestRegion f arg).val s t ↔
      prim f (arg.eval env) s = .fault t := by
  constructor
  · intro fault
    cases fault with
    | br term =>
      cases term with
      | op_arg head => exact (expr_no_fault prim env arg head).elim
      | op_fault head failure =>
        obtain ⟨rfl, rfl⟩ := head.deterministic (instr_deterministic prim env) (expr_eval prim env arg s)
        obtain ⟨_, reply⟩ := failure
        exact reply
  · intro reply
    exact .br (.op_fault (expr_eval prim env arg s) ⟨(arg.eval env).property, reply⟩)

private theorem request_diverge_iff (f : Φ) (arg : Expr Γ (instrSrc f)) (s : σ) :
    External.Diverges (model prim env).raw.instr (model prim env).raw.prim
      (.region (initialEnv prim env) (Program.requestRegion f arg).val s) ↔
      prim f (arg.eval env) s = .diverge := by
  constructor
  · intro div
    cases div.unfold with
    | br head =>
      cases head with
      | op_arg sub => exact (expr_no_diverge prim env arg sub).elim
      | primitive head active =>
        obtain ⟨rfl, rfl⟩ := head.deterministic (instr_deterministic prim env) (expr_eval prim env arg s)
        obtain ⟨_, reply⟩ := active
        exact reply
    | core step => cases step
  · intro reply
    exact .fold (.br (.primitive (expr_eval prim env arg s) ⟨(arg.eval env).property, reply⟩))

@[expose] def replyOutcomes {A : Silmaril.Ty Empty} : StateReply A σ → Set (Outcome 1 Unit (σ))
  | .ret a t => {Outcome.ret 0 a.val t}
  | .fault t => {Outcome.fault t}
  | .diverge => {Outcome.diverge}

theorem observe_request (f : Φ) (arg : Expr Γ (instrSrc f)) (s : σ) :
    denote (.native (Program.requestRegion f arg)) (model prim env).raw s =
      WithTop.some (replyOutcomes (prim f (arg.eval env) s)) := by
  apply congrArg WithTop.some
  ext o
  rw [mem_nativeOutcomes_iff _ (envOfBound_agrees (model prim env).raw.bound)]
  cases o with
  | ret i a t =>
    obtain rfl := Fin.eq_zero i
    exact (request_eval_iff prim env f arg s t a).trans (by
      cases prim f (arg.eval env) s <;> simp [replyOutcomes, StateReply.returns, Set.mem_singleton_iff, eq_comm])
  | fault t =>
    exact (request_fault_iff prim env f arg s t).trans (by
      cases prim f (arg.eval env) s <;> simp [replyOutcomes, Set.mem_singleton_iff, eq_comm])
  | diverge =>
    exact (request_diverge_iff prim env f arg s).trans (by
      cases prim f (arg.eval env) s <;> simp [replyOutcomes, Set.mem_singleton_iff, eq_comm])

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
