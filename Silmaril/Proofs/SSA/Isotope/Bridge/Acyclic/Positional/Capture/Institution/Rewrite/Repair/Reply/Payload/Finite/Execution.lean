module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Replay

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite

open Isotope.Semantics (BoundEnv)
open Isotope.LetCase.LocallyNameless (Derivation)
open Kleisli (value)
open LambdaSSA (At)
open LambdaSSA.Acyclic (FiniteExit Operand)
open LambdaSSA.Region (packedExitType)
open LambdaSSA.Semantics.Categorical (labelAt_get)
open LetIter.Semantics.Categorical (boundEnv)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)

theorem matches_bind_proof {k n : Nat} {β : BoundCtx Sorts k} {slots : Retained β n}
    {ρ : BoundEnv value β} {env : Assignment n} (h : slots.Matches ρ env) (b : Bool) :
    slots.bind.Matches (ρ.snoc (A := Bit) (bit b)) (env.push b) := by
  intro i
  exact Fin.cases rfl h i

theorem run_bit_case_proof {k : Nat} {β : BoundCtx Sorts k} {A : Sorts}
    (ρ : BoundEnv value β) (d : Operand signature.Instr β Bit)
    (l r : Operand signature.Instr (β.snoc U) A) (b : Bool)
    (read : Kleisli.run model d.2 ρ = pure (bit b)) :
    Kleisli.run model (.case d.2 l.2 r.2) ρ =
      Kleisli.run model (if b then r else l).2 (ρ.snoc (A := U) PUnit.unit) := by
  unfold Kleisli.run at read ⊢
  rw [Derivation.denote, read, pure_bind]
  cases b <;> rfl

theorem expr_run_proof {n : Nat} (e : Expr n) {k : Nat} {β : BoundCtx Sorts k}
    (slots : Retained β n) (ρ : BoundEnv value β) (env : Assignment n) (h : slots.Matches ρ env) :
    Kleisli.run model (e.operand slots).2 ρ = pure (bit (e.eval env)) := by
  induction e generalizing k with
  | literal b => exact run_bitOperand ρ b
  | read i => exact run_readPayload ρ (slots i).1 (slots i).2 (env i) (h i)
  | split l r ihl ihr =>
    let older : Retained (β.snoc U) _ := fun i => slots.weaken U i.succ
    let ρ' := ρ.snoc (A := U) PUnit.unit
    have h' : older.Matches ρ' env.tail := fun i => h i.succ
    have read := run_readPayload ρ (slots 0).1 (slots 0).2 (env 0) (h 0)
    change Kleisli.run model (.case (slots.read 0).2 (l.operand older).2 (r.operand older).2) ρ = _
    rw [run_bit_case_proof ρ (slots.read 0) (l.operand older) (r.operand older) (env 0) read]
    cases hb : env 0
    · simp only [Expr.eval, hb, Bool.false_eq_true, ite_false]
      exact ihl older ρ' env.tail h'
    · simp only [Expr.eval, hb, ite_true]
      exact ihr older ρ' env.tail h'

theorem normal_run_proof {L : List Sorts} {n : Nat} (p : Normal L n)
    {k : Nat} {β : BoundCtx Sorts k} (slots : Retained β n)
    (ρ : BoundEnv value β) (env : Assignment n) (h : slots.Matches ρ env)
    (finish : value (packedExitType L) → Trace (value (packedExitType L)))
    (onReturn : ∀ x : Exits.Exit L, finish x.packed = pure x.packed) :
    (Kleisli.run model (p.render.operand slots).2 ρ >>= finish).outcomes = p.outcomes env := by
  induction p generalizing k with
  | ret position table =>
    have run := expr_run_proof (Expr.quote _ table) slots ρ env h
    rw [quote_eval_proof] at run
    have tagged := Exits.run_tag model ρ L _ position.typed _ _ run
    change (Kleisli.run model (FiniteExit.tag L _ position.typed ((Expr.quote _ table).operand slots)).2
      ρ >>= finish).outcomes = _
    rw [tagged, position.pack_result, pure_bind, onReturn]
    rfl
  | emit b next ih =>
    simp only [Normal.render, Tree.operand, Kleisli.run, Derivation.denote, pure_bind, bind_assoc]
    change ((Reply.model.eval (.emit b) PUnit.unit >>= fun u =>
      Kleisli.run model (next.render.operand (slots.weaken U)).2 (ρ.snoc (A := U) u) >>= finish).outcomes) = _
    rw [Reply.model_emit_bind, ih (slots.weaken U) (ρ.snoc (A := U) PUnit.unit) env h]
    rfl
  | request req l r ihl ihr =>
    exact request_run req _ _ ρ finish Exits.Exit.packed _ _
      (fun b => ihl slots.bind (ρ.snoc (A := Bit) (bit b)) (env.push b) (matches_bind_proof h b))
      (fun b => ihr slots.bind (ρ.snoc (A := Bit) (bit b)) (env.push b) (matches_bind_proof h b))
  | testRequest test low ll lr hl hr ihll ihlr ihhl ihhr =>
    let ρ' := ρ.snoc (A := U) PUnit.unit
    let rest := env.without test
    let kept := (slots.without test).weaken U
    let scope := kept.bind
    let left := requestOperand low false (ll.render.operand scope) (lr.render.operand scope)
    let right := requestOperand (!low) false (hl.render.operand scope) (hr.render.operand scope)
    have hKept : kept.Matches ρ' rest := fun i => h (test.succAbove i)
    have read := run_readPayload ρ (slots test).1 (slots test).2 (env test) (h test)
    change (Kleisli.run model (.case (slots.read test).2 left.2 right.2) ρ >>= finish).outcomes = _
    rw [run_bit_case_proof ρ (slots.read test) left right (env test) read]
    cases hb : env test
    · simp only [Normal.outcomes, Normal.traceTree, hb, Bool.false_eq_true, ite_false]
      exact request_run low _ _ ρ' finish Exits.Exit.packed _ _
        (fun b => ihll scope (ρ'.snoc (A := Bit) (bit b)) (rest.push b) (matches_bind_proof hKept b))
        (fun b => ihlr scope (ρ'.snoc (A := Bit) (bit b)) (rest.push b) (matches_bind_proof hKept b))
    · simp only [Normal.outcomes, Normal.traceTree, hb, ite_true]
      exact request_run (!low) _ _ ρ' finish Exits.Exit.packed _ _
        (fun b => ihhl scope (ρ'.snoc (A := Bit) (bit b)) (rest.push b) (matches_bind_proof hKept b))
        (fun b => ihhr scope (ρ'.snoc (A := Bit) (bit b)) (rest.push b) (matches_bind_proof hKept b))

private theorem packed_normal_run (H : Sorts) (L : List Sorts) (p : Normal (H :: L) 0) :
    programOutcomes H L p.render = p.outcomes Fin.elim0 := by
  let T := packedExitType (H :: L)
  let ρ := boundEnv value (β := .nil) PUnit.unit
  let body := ((program H L p.render).body.render .base).encode.toLetCase.2
  let finish (x : value T) := Kleisli.run model body (ρ.snoc (A := T) x)
  have ret (x : Exits.Exit (H :: L)) : finish x.packed = pure x.packed :=
    Exits.run_router model (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))
      .base ρ x.1 (labelAt_get (H :: L) x.1) x.2
  exact normal_run_proof p Fin.elim0 ρ Fin.elim0 (fun i => i.elim0) finish ret

theorem programOutcomes_eq_of_sat_proof (H : Sorts) (L : List Sorts) (p q : Tree (H :: L) 0)
    (h : ((LetCase.inst Γ₀).obj signature).Sat (Kleisli.algebra model) (grammarCase (equation H L p q))) :
    programOutcomes H L p = programOutcomes H L q :=
  congrArg Tagged.outcomes (Kleisli.run_eq_of_sat model (equation H L p q) h PUnit.unit)

theorem programOutcomes_proof (H : Sorts) (L : List Sorts) (p : Tree (H :: L) 0) :
    programOutcomes H L p = p.normal.outcomes Fin.elim0 :=
  (programOutcomes_eq_of_sat_proof H L p p.normal.render
    (Kleisli.sat_of_repaired model model_respectsPure _ (Repaired.ofNative (derive_render_proof H L p)))).trans
    (packed_normal_run H L p.normal)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite
