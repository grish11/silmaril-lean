module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.RequestTree.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.RequestTree.Soundness

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exit Instr Tag result_order)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration (Result)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (emptyBindings)

private def shift {n : Nat} : Result 2 n → Result 2 (n + 1)
  | .ret i s => .ret i s.succ
  | .fault s => .fault s.succ
  | .diverge => .diverge
  | .ub => .ub

private theorem shift_order {n : Nat} (p q : Result 2 n) :
    (shift p).refines (shift q) ↔ p.refines q := by
  cases p <;> cases q <;> simp [shift, Result.refines]

private theorem execute_succ {n : Nat} (p : Tree) (rest : Prefix n) (f : Instr) (i : Tag)
    (s : Fin (n + 1)) :
    p.execute (Prefix.step f i rest).handler s.succ = shift (p.execute rest.handler s) := by
  induction p generalizing s with
  | stop e => cases e <;> rfl
  | ask g l r left right =>
    rw [Tree.execute, Tree.execute, Prefix.handler_succ]
    cases rest.handler g s with
    | reply j t =>
      by_cases h : j = 0
      · simpa [h] using left t
      · simpa [h] using right t
    | fault | diverge => rfl

private theorem execute_step {n : Nat} (l r : Tree) (rest : Prefix n) (f : Instr) (i : Tag) :
    (Tree.ask f l r).execute (Prefix.step f i rest).handler 0 =
      shift (if i = 0 then l.execute rest.handler 0 else r.execute rest.handler 0) := by
  have entry : (Prefix.step f i rest).handler f 0 = .reply i (Fin.succ 0) := by
    change (if f = f then _ else _) = _
    simp
  rw [Tree.execute, entry]
  by_cases h : i = 0
  · simpa [h] using execute_succ l rest f i 0
  · simpa [h] using execute_succ r rest f i 0

private theorem exit_result_order {n : Nat} (p q : Exit) (s : Fin n) :
    (p.result s).refines (q.result s) ↔ p.Refines q := by
  cases p <;> cases q <;> simp [Exit.result, Exit.Refines, Result.refines]

private theorem prepend {n : Nat} (f : Instr) (l r l' r' : Tree) (i : Tag) (rest : Prefix n)
    (fails : ¬ (if i = 0 then l.execute rest.handler 0 else r.execute rest.handler 0).refines
      (if i = 0 then l'.execute rest.handler 0 else r'.execute rest.handler 0)) :
    ¬ ((Tree.ask f l r).execute (Prefix.step f i rest).handler 0).refines
      ((Tree.ask f l' r').execute (Prefix.step f i rest).handler 0) := by
  rw [execute_step, execute_step, shift_order]
  exact fails

private theorem separate (p q : Tree) (fails : ¬ p.Refines q) :
    ∃ (n : Nat) (probe : Prefix n), n ≤ min p.depth q.depth ∧
      ¬ (p.execute probe.handler 0).refines (q.execute probe.handler 0) := by
  classical
  induction p generalizing q with
  | stop e =>
    cases q with
    | stop e' =>
      exact ⟨0, .stop none, Nat.zero_le _, fun h => fails ((exit_result_order e e' 0).mp h)⟩
    | ask g l r =>
      refine ⟨0, .stop none, Nat.zero_le _, ?_⟩
      cases e <;> simp [Tree.execute, Prefix.handler, Exit.result, Result.refines]
  | ask f l r left right =>
    cases q with
    | stop e =>
      cases e with
      | ub => exact (fails trivial).elim
      | ret i =>
        exact ⟨0, .stop none, Nat.zero_le _, by
          simp [Tree.execute, Prefix.handler, Exit.result, Result.refines]⟩
    | ask g l' r' =>
      by_cases keys : f = g
      · subst g
        by_cases matchedLeft : l.Refines l'
        · have failedRight : ¬ r.Refines r' := fun hr => fails ⟨rfl, matchedLeft, hr⟩
          obtain ⟨n, rest, bound, bad⟩ := right r' failedRight
          refine ⟨n + 1, .step f 1 rest, ?_, prepend f l r l' r' 1 rest ?_⟩
          · exact Nat.le_min.mpr ⟨Nat.succ_le_succ
                ((Nat.le_min.mp bound).1.trans (Nat.le_max_right _ _)),
              Nat.succ_le_succ ((Nat.le_min.mp bound).2.trans (Nat.le_max_right _ _))⟩
          · simpa using bad
        · obtain ⟨n, rest, bound, bad⟩ := left l' matchedLeft
          refine ⟨n + 1, .step f 0 rest, ?_, prepend f l r l' r' 0 rest ?_⟩
          · exact Nat.le_min.mpr ⟨Nat.succ_le_succ
                ((Nat.le_min.mp bound).1.trans (Nat.le_max_left _ _)),
              Nat.succ_le_succ ((Nat.le_min.mp bound).2.trans (Nat.le_max_left _ _))⟩
          · simpa using bad
      · exact ⟨0, .stop (some f), Nat.zero_le _, by
          simp [Tree.execute, Prefix.handler, keys, Result.refines]⟩

theorem exists_prefix_countermodel {p q : Tree} (fails : ¬ p.Refines q) :
    ∃ (n : Nat) (probe : Prefix n), n ≤ min p.depth q.depth ∧
      ¬ Shape.denote p.region probe.handler.model 0 ≤ Shape.denote q.region probe.handler.model 0 := by
  obtain ⟨n, probe, bound, bad⟩ := separate p q fails
  refine ⟨n, probe, bound, ?_⟩
  rw [finite_observe p probe.handler emptyBindings 0, finite_observe q probe.handler emptyBindings 0,
    result_order]
  exact bad

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree
