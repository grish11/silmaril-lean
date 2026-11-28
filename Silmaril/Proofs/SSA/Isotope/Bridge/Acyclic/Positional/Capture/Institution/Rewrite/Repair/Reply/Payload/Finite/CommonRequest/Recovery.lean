module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms
import Mathlib.Data.Fin.Tuple.Basic

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest

private theorem push_tail {n : Nat} (env : Assignment (n + 1)) :
    env.tail.push (env 0) = env := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem normal_inj_proof {L : List Sorts} {n : Nat} (test : Fin (n + 1)) (p q : NormalSource L n)
    (h : ∀ env, p.outcomes test env = q.outcomes test env) : p = q := by
  have paths (env : Assignment (n + 1)) : p.traceTree test env = q.traceTree test env :=
    Reply.Normal.outcomesWith_injective _ (Exits.Exit.packed_injective L) (h env)
  have split (b : Bool) (rest : Assignment n) :
      (if b then requestTree p.request (fun a => p.arms.trueLeft.traceTree (rest.push a))
          (fun a => p.arms.trueRight.traceTree (rest.push a))
        else requestTree p.request (fun a => p.arms.falseLeft.traceTree (rest.push a))
          (fun a => p.arms.falseRight.traceTree (rest.push a))) =
      (if b then requestTree q.request (fun a => q.arms.trueLeft.traceTree (rest.push a))
          (fun a => q.arms.trueRight.traceTree (rest.push a))
        else requestTree q.request (fun a => q.arms.falseLeft.traceTree (rest.push a))
          (fun a => q.arms.falseRight.traceTree (rest.push a))) := by
    let env : Assignment (n + 1) := Fin.insertNth (α := fun _ => Bool) test b rest
    have slot : env test = b := Fin.insertNth_apply_same (α := fun _ => Bool) test b rest
    have kept : env.without test = rest := funext (Fin.insertNth_apply_succAbove (α := fun _ => Bool) test b rest)
    simpa only [NormalSource.traceTree, slot, kept] using paths env
  have low (env : Assignment (n + 1)) :
      p.request = q.request ∧
        (∀ b, p.arms.falseLeft.traceTree (env.tail.push b) = q.arms.falseLeft.traceTree (env.tail.push b)) ∧
        (∀ b, p.arms.falseRight.traceTree (env.tail.push b) = q.arms.falseRight.traceTree (env.tail.push b)) := by
    apply requestTree_inj
    simpa only [Bool.false_eq_true, ite_false] using split false env.tail
  have high (env : Assignment (n + 1)) :
      p.request = q.request ∧
        (∀ b, p.arms.trueLeft.traceTree (env.tail.push b) = q.arms.trueLeft.traceTree (env.tail.push b)) ∧
        (∀ b, p.arms.trueRight.traceTree (env.tail.push b) = q.arms.trueRight.traceTree (env.tail.push b)) := by
    apply requestTree_inj
    simpa only [ite_true] using split true env.tail
  have sameRequest := (low (fun _ => false)).1
  have ll := p.arms.falseLeft.traceTree_inj q.arms.falseLeft fun env =>
    by simpa only [push_tail] using (low env).2.1 (env 0)
  have lr := p.arms.falseRight.traceTree_inj q.arms.falseRight fun env =>
    by simpa only [push_tail] using (low env).2.2 (env 0)
  have hl := p.arms.trueLeft.traceTree_inj q.arms.trueLeft fun env =>
    by simpa only [push_tail] using (high env).2.1 (env 0)
  have hr := p.arms.trueRight.traceTree_inj q.arms.trueRight fun env =>
    by simpa only [push_tail] using (high env).2.2 (env 0)
  cases p with
  | mk req arms =>
    cases q with
    | mk req' arms' =>
      cases arms
      cases arms'
      cases sameRequest
      cases ll
      cases lr
      cases hl
      cases hr
      rfl

theorem after_request_proof {L : List Sorts} {n : Nat} (p : NormalSource L n) (test : Fin (n + 1))
    (env : Assignment (n + 1)) (right b : Bool) :
    afterPayload p.request right b (p.outcomes test env) =
      (if env test then (if right then p.arms.trueRight else p.arms.trueLeft)
        else (if right then p.arms.falseRight else p.arms.falseLeft)).outcomes ((env.without test).push b) := by
  cases h : env test <;> cases right <;>
    simp only [NormalSource.outcomes, NormalSource.traceTree, h, Bool.false_eq_true, ite_false, ite_true] <;>
    exact afterRequest Exits.Exit.packed _ _ _ _ b

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest
