module

public import Silmaril.SSA.MLIR.SCF.LetIter.Behaviour

/-! # Agreement with the native LetIter lowering -/

public section

universe u v w

namespace Silmaril.MLIR.SCF.LetIter.RegionLoop

open Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational (Model Observation noFree iterBeh)
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.Semantics

variable {Φ : Type u} {n : Nat} {M : Model.{u, v, w} Φ n} {p : RegionLoop Φ n}

private theorem body_exit_iff {c : Entry M} {out : Value M.α} {s : M.σ} :
    Eval M.instr noFree (extend M.bound c.1) p.iterBody c.2 (.inl out) s ↔ p.Exit M c out s := by
  constructor
  · intro run
    cases run with
    | case_inl test branch =>
        cases branch with
        | inl arg =>
            obtain ⟨rfl, rfl⟩ := eval_bv_result arg
            exact test
    | case_inr _ branch => cases branch
  · exact fun h => .case_inl h (.inl .bv)

private theorem body_backedge_iff {c d : Entry M} :
    Eval M.instr noFree (extend M.bound c.1) p.iterBody c.2 (.inr d.1) d.2 ↔ p.Backedge M c d := by
  constructor
  · intro run
    cases run with
    | case_inl _ branch => cases branch
    | case_inr test branch =>
        cases branch with
        | inr arg => exact ⟨_, _, test, eval_underBinder_iff.mp arg⟩
  · rintro ⟨_, _, test, afterRegion⟩
    exact .case_inr test (.inr (eval_underBinder_iff.mpr afterRegion))

private theorem body_fault_iff {c : Entry M} {s : M.σ} :
    Fault M.instr M.faults noFree (extend M.bound c.1) p.iterBody c.2 s ↔ p.IterationFault M c s := by
  constructor
  · intro run
    cases run with
    | case_arg test => exact Or.inl test
    | case_inl _ branch => cases branch with | inl arg => cases arg
    | case_inr test branch =>
        cases branch with
        | inr arg => exact Or.inr ⟨_, _, test, fault_underBinder_iff.mp arg⟩
  · rintro (test | ⟨_, _, test, afterRegion⟩)
    · exact .case_arg test
    · exact .case_inr test (.inr (fault_underBinder_iff.mpr afterRegion))

private theorem body_diverges_iff {c : Entry M} :
    External.Diverges M.instr noFree M.prim (.term (extend M.bound c.1) p.iterBody c.2) ↔
      p.IterationDiverges M c := by
  constructor
  · intro div
    cases div.unfold with
    | core h => cases h with
      | case_scrutinee test => exact Or.inl test
      | case_inl _ branch =>
          cases branch.unfold with
          | core h => cases h with
            | inl arg => cases arg.unfold with | core h => cases h
      | case_inr test branch =>
          cases branch.unfold with
          | core h => cases h with
            | inr arg => exact Or.inr ⟨_, _, test, diverges_underBinder_iff.mp arg⟩
  · rintro (test | ⟨_, _, test, afterRegion⟩)
    · exact .fold_core (.case_scrutinee test)
    · exact .fold_core (.case_inr test (.fold_core (.inr (diverges_underBinder_iff.mpr afterRegion))))

/-- A native iteration returns exactly on a false condition after finitely many yields. -/
theorem loopReturns_iff {c : Entry M} {out : Value M.α} {s : M.σ} :
    p.LoopReturns M c out s ↔ Loop M.instr noFree M.bound p.iterBody c.1 c.2 out s := by
  constructor
  · rintro ⟨d, path, exit⟩
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact .done (body_exit_iff.mpr exit)
    | head step _ ih => exact .step (body_backedge_iff.mpr step) ih
  · intro run
    exact Loop.induction_fixed
      (motive := fun cur st value final => p.LoopReturns M (cur, st) value final)
      (fun h => ⟨_, .refl, body_exit_iff.mp h⟩)
      (fun h _ ⟨d, path, exit⟩ => ⟨d, path.head (body_backedge_iff.mp h), exit⟩) run

/-- A native iteration faults exactly at a region fault reached by finitely many yields. -/
theorem loopFaults_iff {c : Entry M} {s : M.σ} :
    p.LoopFaults M c s ↔ LoopFault M.instr M.faults noFree M.bound p.iterBody c.1 c.2 s := by
  constructor
  · rintro ⟨d, path, fault⟩
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact .body (body_fault_iff.mpr fault)
    | head step _ ih => exact .step (body_backedge_iff.mpr step) ih
  · intro run
    exact LoopFault.induction_fixed
      (motive := fun cur st final => p.LoopFaults M (cur, st) final)
      (fun h => ⟨_, .refl, body_fault_iff.mp h⟩)
      (fun h _ ⟨d, path, fault⟩ => ⟨d, path.head (body_backedge_iff.mp h), fault⟩) run

/-- The native iteration and the region boundary have the same divergence,
including divergence inside either region and infinitely many successful yields. -/
theorem loopDiverges_iff {c : Entry M} :
    p.LoopDiverges M c ↔
      External.Diverges M.instr noFree M.prim (.loop M.bound p.iterBody c.1 c.2) := by
  constructor
  · rintro ⟨R, hc, closed⟩
    let S := fun cfg : Config M.α Empty Φ M.σ =>
      (∃ d : Entry M, cfg = .loop M.bound p.iterBody d.1 d.2 ∧ R d) ∨
        External.Diverges M.instr noFree M.prim cfg
    refine External.Diverges.coinduct S ?_ (Or.inl ⟨c, rfl, hc⟩)
    rintro cfg (⟨d, rfl, hd⟩ | div)
    · rcases closed d hd with h | ⟨e, step, he⟩
      · exact .core (.loop_body (Or.inr (body_diverges_iff.mpr h)))
      · exact .core (.loop_step (body_backedge_iff.mpr step) (Or.inl ⟨e, rfl, he⟩))
    · exact div.unfold.mono (fun _ h => Or.inr h)
  · intro h
    refine ⟨fun d => External.Diverges M.instr noFree M.prim (.loop M.bound p.iterBody d.1 d.2),
      h, ?_⟩
    intro d div
    cases div.unfold with
    | core h => cases h with
      | loop_body body => exact Or.inl (body_diverges_iff.mp body)
      | loop_step step tail => exact Or.inr ⟨(_, _), body_backedge_iff.mp step, tail⟩

private theorem observe_ret_iff {s s' : M.σ} {out : Value M.α} :
    Observation.ret s out s' ∈ p.observe M ↔ Eval M.instr noFree M.bound p.lower s out s' := by
  constructor
  · rintro ⟨_, _, _, _, init, loop, parent⟩
    exact .let₁ (.iter init (loopReturns_iff.mp loop)) parent
  · intro run
    cases run with
    | let₁ loop parent => cases loop with
      | iter init loop => exact ⟨_, _, _, _, init, loopReturns_iff.mpr loop, parent⟩

private theorem observe_fault_iff {s s' : M.σ} :
    Observation.fault s s' ∈ p.observe M ↔ Fault M.instr M.faults noFree M.bound p.lower s s' := by
  constructor
  · rintro (init | ⟨_, _, init, loop | ⟨_, _, loop, parent⟩⟩)
    · exact .let₁_arg (.iter_init init)
    · exact .let₁_arg (.iter_loop init (loopFaults_iff.mp loop))
    · exact .let₁_body (.iter init (loopReturns_iff.mp loop)) parent
  · intro run
    cases run with
    | let₁_arg iter => cases iter with
      | iter_init init => exact Or.inl init
      | iter_loop init loop => exact Or.inr ⟨_, _, init, Or.inl (loopFaults_iff.mpr loop)⟩
    | let₁_body iter parent => cases iter with
      | iter init loop => exact Or.inr ⟨_, _, init, Or.inr ⟨_, _, loopReturns_iff.mpr loop, parent⟩⟩

private theorem observe_diverge_iff {s : M.σ} :
    Observation.diverge s ∈ p.observe M ↔
      External.Diverges M.instr noFree M.prim (.term M.bound p.lower s) := by
  constructor
  · rintro (init | ⟨_, _, init, loop | ⟨_, _, loop, parent⟩⟩)
    · exact .fold_core (.let₁_arg (.fold_core (.iter_init init)))
    · exact .fold_core (.let₁_arg (.fold_core (.iter_loop init (loopDiverges_iff.mp loop))))
    · exact .fold_core (.let₁_body (.iter init (loopReturns_iff.mp loop)) parent)
  · intro div
    cases div.unfold with
    | core h => cases h with
      | let₁_arg iter => cases iter.unfold with
        | core h => cases h with
          | iter_init init => exact Or.inl init
          | iter_loop init loop => exact Or.inr ⟨_, _, init, Or.inl (loopDiverges_iff.mpr loop)⟩
      | let₁_body iter parent => cases iter with
        | iter init loop => exact Or.inr ⟨_, _, init, Or.inr ⟨_, _, loopReturns_iff.mpr loop, parent⟩⟩

/-- Lowering preserves and reflects full parent answers at every native model. -/
theorem observe_eq_iterBeh : p.observe M = iterBeh M p.lower :=
  Observation.set_eq_iff.mpr
    ⟨fun _ _ _ => observe_ret_iff, fun _ _ => observe_fault_iff, fun _ => observe_diverge_iff⟩

end Silmaril.MLIR.SCF.LetIter.RegionLoop
