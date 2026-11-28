module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Replay

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest

open Isotope.Semantics (BoundEnv)
open Isotope.LetCase.LocallyNameless (Derivation)
open Kleisli (value)
open LambdaSSA (At)
open LambdaSSA.Region (packedExitType)
open LambdaSSA.Semantics.Categorical (labelAt_get)
open LetIter.Semantics.Categorical (boundEnv boundEnv_snoc)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)

theorem bitSlots_matches_proof (n : Nat) (env : Assignment n) :
    (bitSlots n).Matches (boundEnv value (packedAssignment n env)) env := by
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih =>
    change (bitSlots n).bind.Matches
      (boundEnv value (β := (bitCtx n).snoc Bit) (packedAssignment n env.tail, bit (env 0))) env
    rw [boundEnv_snoc]
    have h := (ih env.tail).bind (env 0)
    intro i
    exact Fin.cases rfl (fun j => h j.succ) i

private theorem packed_normal_run (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1))
    (p : NormalSource (H :: L) n) (env : Assignment (n + 1)) :
    programOutcomes H L test p.render env = p.outcomes test env := by
  let T := packedExitType (H :: L)
  let slots := bitSlots (n + 1)
  let ρ := boundEnv value (packedAssignment (n + 1) env)
  let rest := env.without test
  let ρ' := ρ.snoc (A := U) PUnit.unit
  let kept := (slots.without test).weaken U
  let body := ((program H L test p.render).body.render .base).encode.toLetCase.2
  let finish (x : value T) := Kleisli.run model body (ρ.snoc (A := T) x)
  have ret (x : Exits.Exit (H :: L)) : finish x.packed = pure x.packed :=
    Exits.run_router model (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))
      .base ρ x.1 (labelAt_get (H :: L) x.1) x.2
  have keptMatches : kept.Matches ρ' rest := fun i => bitSlots_matches_proof _ env (test.succAbove i)
  have read := run_readPayload ρ (slots test).1 (slots test).2 (env test) (bitSlots_matches_proof _ env test)
  let l := requestOperand p.request false
    (p.arms.falseLeft.render.operand kept.bind) (p.arms.falseRight.render.operand kept.bind)
  let r := requestOperand p.request false
    (p.arms.trueLeft.render.operand kept.bind) (p.arms.trueRight.render.operand kept.bind)
  change (Kleisli.run model (.case (slots.read test).2 l.2 r.2) ρ >>= finish).outcomes = _
  rw [run_bit_case ρ (slots.read test) l r (env test) read]
  have runArm (arm : Normal (H :: L) (n + 1)) (b : Bool) :=
    arm.run kept.bind (ρ'.snoc (A := Bit) (bit b)) (rest.push b) (keptMatches.bind b) finish ret
  cases h : env test
  · simp only [NormalSource.outcomes, NormalSource.traceTree, h, Bool.false_eq_true, ite_false]
    exact request_run _ _ _ ρ' finish Exits.Exit.packed _ _ (runArm p.arms.falseLeft) (runArm p.arms.falseRight)
  · simp only [NormalSource.outcomes, NormalSource.traceTree, h, ite_true]
    exact request_run _ _ _ ρ' finish Exits.Exit.packed _ _ (runArm p.arms.trueLeft) (runArm p.arms.trueRight)

theorem programOutcomes_eq_of_sat_proof (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1))
    (p q : Source (H :: L) n)
    (h : ((LetCase.inst Γ₀).obj signature).Sat (Kleisli.algebra model) (grammarCase (equation H L test p q)))
    (env : Assignment (n + 1)) :
    programOutcomes H L test p env = programOutcomes H L test q env :=
  congrArg Tagged.outcomes (Kleisli.run_eq_of_sat model (equation H L test p q) h (packedAssignment _ env))

theorem programOutcomes_proof (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1))
    (p : Source (H :: L) n) (env : Assignment (n + 1)) :
    programOutcomes H L test p env = p.normal.outcomes test env := by
  have normalized : Derivable false (equation H L test p p.normal.render) :=
    .let₁ (source_replay_proof p (bitSlots _) test)
      (.refl ((program H L test p).body.render .base).encode.toLetCase.2.toHasType)
  have sat := Kleisli.sat_of_repaired model model_respectsPure _ (Repaired.ofNative normalized)
  exact (programOutcomes_eq_of_sat_proof H L test p p.normal.render sat env).trans
    (packed_normal_run H L test p.normal env)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest
