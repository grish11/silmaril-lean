module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms
import Mathlib.Data.Fin.Tuple.Basic
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Replay

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite

private def nextRequest {R : Type} : Reply.Normal R → Option Bool
  | .ask req _ _ => some req
  | _ => none

private theorem next_request_test {L : List Sorts} {n : Nat}
    (test : Fin (n + 1)) (low : Bool) (ll lr hl hr : Normal L (n + 1)) (env : Assignment (n + 1)) :
    nextRequest ((Normal.testRequest test low ll lr hl hr).traceTree env) =
      some (if env test then !low else low) := by
  cases h : env test <;>
    simp only [Normal.traceTree, h, Bool.false_eq_true, ite_true, ite_false, requestTree, nextRequest]

private theorem distinct_label (low : Bool) : low ≠ !low := by
  cases low <;> decide

private theorem test_label_inj {n : Nat} {i j : Fin (n + 1)} {low low' : Bool}
    (h : ∀ env : Assignment (n + 1), (if env i then !low else low) = (if env j then !low' else low')) :
    i = j ∧ low = low' := by
  have label : low = low' := h (fun _ => false)
  subst low'
  refine ⟨?_, rfl⟩
  by_contra different
  have probe := h (fun k => decide (k = i))
  simp only [decide_true, ite_true, decide_eq_false (Ne.symm different), Bool.false_eq_true, ite_false] at probe
  exact distinct_label low probe.symm

private theorem erase_insert {n : Nat} (env : Assignment n) (test : Fin (n + 1)) (b : Bool) :
    Assignment.without (Fin.insertNth (α := fun _ => Bool) test b env) test = env := by
  funext i
  exact Fin.insertNth_apply_succAbove (α := fun _ => Bool) test b env i

private theorem recover_extensions {L : List Sorts} {n : Nat} {p q : Normal L (n + 1)}
    (h : ∀ (env : Assignment n) b, p.traceTree (env.push b) = q.traceTree (env.push b)) :
    ∀ env, p.traceTree env = q.traceTree env := by
  intro env
  simpa only [assignment_eta_proof] using h env.tail (env 0)

theorem traceTree_inj_proof {L : List Sorts} {n : Nat} (p : Normal L n) :
    ∀ q : Normal L n, (∀ env, p.traceTree env = q.traceTree env) → p = q := by
  induction p with
  | ret position table =>
    intro q h
    cases q with
    | ret position' table' =>
      have entry (env : Assignment _) := Position.result_inj (Reply.Normal.ret.inj (h env))
      exact congrArg₂ Normal.ret (entry (fun _ => false)).1 (funext fun env => (entry env).2)
    | emit | request | testRequest =>
      have head := h (fun _ => false)
      cases head
  | emit label p ih =>
    intro q h
    cases q with
    | emit label' q =>
      have step (env : Assignment _) := Reply.Normal.emit.inj (h env)
      exact congrArg₂ Normal.emit (step (fun _ => false)).1 (ih q fun env => (step env).2)
    | ret | request | testRequest =>
      have head := h (fun _ => false)
      cases head
  | request req l r ihl ihr =>
    intro q h
    cases q with
    | request req' l' r' =>
      have step (env : Assignment _) := requestTree_inj (h env)
      rw [(step (fun _ => false)).1,
        ihl l' (recover_extensions (fun env b => (step env).2.1 b)),
        ihr r' (recover_extensions (fun env b => (step env).2.2 b))]
    | ret | emit =>
      have head := h (fun _ => false)
      cases head
    | testRequest test low ll lr hl hr =>
      have labels (env : Assignment _) := congrArg nextRequest (h env)
      have lf : req = low := Option.some.inj (labels (fun _ => false))
      have lt : req = !low := Option.some.inj (labels (fun _ => true))
      exact False.elim (distinct_label low (lf.symm.trans lt))
  | testRequest test low ll lr hl hr ihll ihlr ihhl ihhr =>
    intro q h
    cases q with
    | ret | emit =>
      have head := h (fun _ => false)
      cases head
    | request req l r =>
      have labels (env : Assignment _) := congrArg nextRequest (h env)
      have lf : low = req := Option.some.inj (labels (fun _ => false))
      have lt : (!low) = req := Option.some.inj (labels (fun _ => true))
      exact False.elim (distinct_label low (lf.trans lt.symm))
    | testRequest test' low' ll' lr' hl' hr' =>
      have labels (env : Assignment _) := congrArg nextRequest (h env)
      have key := test_label_inj (i := test) (j := test') (low := low) (low' := low') (fun env => by
        have eq := labels env
        rw [next_request_test, next_request_test] at eq
        exact Option.some.inj eq)
      obtain ⟨rfl, rfl⟩ := key
      have whenFalse (env : Assignment _) :
          (∀ b, ll.traceTree (env.push b) = ll'.traceTree (env.push b)) ∧
          (∀ b, lr.traceTree (env.push b) = lr'.traceTree (env.push b)) := by
        have eq := h (Fin.insertNth (α := fun _ => Bool) test false env)
        simp only [Normal.traceTree, Fin.insertNth_apply_same, Bool.false_eq_true, ite_false, erase_insert] at eq
        exact (requestTree_inj eq).2
      have whenTrue (env : Assignment _) :
          (∀ b, hl.traceTree (env.push b) = hl'.traceTree (env.push b)) ∧
          (∀ b, hr.traceTree (env.push b) = hr'.traceTree (env.push b)) := by
        have eq := h (Fin.insertNth (α := fun _ => Bool) test true env)
        simp only [Normal.traceTree, Fin.insertNth_apply_same, ite_true, erase_insert] at eq
        exact (requestTree_inj eq).2
      rw [ihll ll' (recover_extensions (fun env => (whenFalse env).1)),
        ihlr lr' (recover_extensions (fun env => (whenFalse env).2)),
        ihhl hl' (recover_extensions (fun env => (whenTrue env).1)),
        ihhr hr' (recover_extensions (fun env => (whenTrue env).2))]

theorem outcomes_injective_proof (L : List Sorts) :
    Function.Injective (fun p : Normal L 0 => p.outcomes Fin.elim0) := by
  intro p q h
  apply traceTree_inj_proof p q
  intro env
  have empty : env = Fin.elim0 := funext fun i => i.elim0
  rw [empty]
  exact Reply.Normal.outcomesWith_injective _ (Exits.Exit.packed_injective L) h

theorem after_request_proof {L : List Sorts} {n : Nat} (req : Bool) (l r : Normal L (n + 1))
    (env : Assignment n) (right b : Bool) :
    afterPayload req right b ((Normal.request req l r).outcomes env) =
      (if right then r else l).outcomes (env.push b) := by
  cases right <;> exact afterRequest Exits.Exit.packed req
    (fun bit => l.traceTree (env.push bit)) (fun bit => r.traceTree (env.push bit)) _ b

theorem after_test_request_proof {L : List Sorts} {n : Nat}
    (test : Fin (n + 1)) (low : Bool) (ll lr hl hr : Normal L (n + 1))
    (env : Assignment (n + 1)) (right b : Bool) :
    afterPayload (if env test then !low else low) right b
        ((Normal.testRequest test low ll lr hl hr).outcomes env) =
      (if env test then (if right then hr else hl) else (if right then lr else ll)).outcomes
        ((env.without test).push b) := by
  cases h : env test
  · simp only [h, Bool.false_eq_true, ite_false, Normal.outcomes, Normal.traceTree]
    exact after_request_proof low ll lr (env.without test) right b
  · simp only [h, ite_true, Normal.outcomes, Normal.traceTree]
    exact after_request_proof (!low) hl hr (env.without test) right b

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite
