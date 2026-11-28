module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Soundness

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exit result_order)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration (Result)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (Expr Payload emptyBindings)

universe u

variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)] [DecidableEq Φ] {R : Φ → List (Silmaril.Ty Empty)}

private def shift {n : Nat} : Result 2 n → Result 2 (n + 1)
  | .ret i s => .ret i s.succ
  | .fault s => .fault s.succ
  | .diverge => .diverge
  | .ub => .ub

private theorem shift_order {n : Nat} (p q : Result 2 n) :
    (shift p).refines (shift q) ↔ p.refines q := by
  cases p <;> cases q <;> simp [shift, Result.refines]

private theorem execute_succ {n : Nat} (p : Tree R) (rest : Prefix R n) (f : Φ) (input : Value Unit)
    (i : Fin (R f).length) (a : Payload ((R f).get i)) (s : Fin (n + 1)) :
    p.execute (Prefix.step f input i a rest).handler s.succ = shift (p.execute rest.handler s) := by
  induction p generalizing s with
  | stop e => cases e <;> rfl
  | ask g arg arms ih =>
    rw [Tree.execute, Tree.execute, Prefix.handler_succ]
    cases rest.handler g (operandValue arg) s with
    | reply j _ t => exact ih j t
    | fault | diverge => rfl

private theorem execute_step {n : Nat} (f : Φ) (arg : Expr [] (instrSrc f))
    (arms : Fin (R f).length → Tree R) (input : Value Unit) (same : input = operandValue arg)
    (i : Fin (R f).length) (a : Payload ((R f).get i)) (rest : Prefix R n) :
    (Tree.ask f arg arms).execute (Prefix.step f input i a rest).handler 0 =
      shift ((arms i).execute rest.handler 0) := by
  subst input
  have entry : (Prefix.step f (operandValue arg) i a rest).handler f (operandValue arg) 0 =
      .reply i a (Fin.succ 0) := by
    simp [Prefix.handler]
  rw [Tree.execute, entry]
  exact execute_succ (arms i) rest f (operandValue arg) i a 0

private theorem exit_result_order {n : Nat} (p q : Exit) (s : Fin n) :
    (p.result s).refines (q.result s) ↔ p.Refines q := by
  cases p <;> cases q <;> simp [Exit.result, Exit.Refines, Result.refines]

private theorem separate (p q : Tree R) (fails : ¬ p.Refines q) :
    ∃ (n : Nat) (probe : Prefix R n), n ≤ min p.depth q.depth ∧
      ¬ (p.execute probe.handler 0).refines (q.execute probe.handler 0) := by
  classical
  induction p generalizing q with
  | stop e =>
    cases q with
    | stop e' =>
      exact ⟨0, .stop none, Nat.zero_le _, fun h => fails ((exit_result_order e e' 0).mp h)⟩
    | ask g arg arms =>
      refine ⟨0, .stop none, Nat.zero_le _, ?_⟩
      cases e <;> simp [Tree.execute, Prefix.handler, Exit.result, Result.refines]
  | ask f arg arms ih =>
    cases q with
    | stop e =>
      cases e with
      | ub => exact (fails trivial).elim
      | ret i =>
        exact ⟨0, .stop none, Nat.zero_le _, by
          simp [Tree.execute, Prefix.handler, Exit.result, Result.refines]⟩
    | ask g arg' next =>
      by_cases query : (f, operandValue arg) = (g, operandValue arg')
      · obtain ⟨keys, inputs⟩ := Prod.mk.inj query
        subst g
        have missed : ∃ i, Nonempty (Payload ((R f).get i)) ∧ ¬ (arms i).Refines (next i) := by
          by_contra missing
          exact fails ⟨rfl, inputs, fun i available => Classical.byContradiction fun bad =>
            missing ⟨i, available, bad⟩⟩
        obtain ⟨i, ⟨a⟩, bad⟩ := missed
        obtain ⟨n, rest, bound, counterexample⟩ := ih i (next i) bad
        refine ⟨n + 1, .step f (operandValue arg) i a rest, ?_, ?_⟩
        · have maxLeft : (arms i).depth ≤ Finset.univ.sup (fun j => (arms j).depth) :=
            Finset.le_sup (f := fun j => (arms j).depth) (Finset.mem_univ i)
          have maxRight : (next i).depth ≤ Finset.univ.sup (fun j => (next j).depth) :=
            Finset.le_sup (f := fun j => (next j).depth) (Finset.mem_univ i)
          exact Nat.le_min.mpr ⟨Nat.succ_le_succ ((Nat.le_min.mp bound).1.trans maxLeft),
            Nat.succ_le_succ ((Nat.le_min.mp bound).2.trans maxRight)⟩
        · rw [execute_step f arg arms _ rfl, execute_step f arg' next _ inputs, shift_order]
          exact counterexample
      · refine ⟨0, .stop (some (f, operandValue arg)), Nat.zero_le _, ?_⟩
        have off : ¬ (f = g ∧ operandValue arg = operandValue arg') :=
          fun ⟨key, input⟩ => query (Prod.ext key input)
        simp [Tree.execute, Prefix.handler, off, Result.refines]

theorem exists_prefix_countermodel {S : RequestSignature Φ} {p q : Tree S.replies}
    (fails : ¬ p.Refines q) :
    ∃ (n : Nat) (probe : Prefix S.replies n), n ≤ min p.depth q.depth ∧
      ¬ Shape.denote (p.region S) (S.model probe.handler) 0 ≤
        Shape.denote (q.region S) (S.model probe.handler) 0 := by
  obtain ⟨n, probe, bound, bad⟩ := separate p q fails
  refine ⟨n, probe, bound, ?_⟩
  rw [finite_observe p probe.handler emptyBindings 0, finite_observe q probe.handler emptyBindings 0,
    result_order]
  exact bad

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
