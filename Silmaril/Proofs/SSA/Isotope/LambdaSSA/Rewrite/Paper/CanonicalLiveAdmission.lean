module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.CanonicalLive.Admission.Defs

/-! # The admitted comparison always decides -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveAdmission

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.OpenReplay
open CanonicalLive
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

private theorem assignment_mem : ∀ {n : Nat} (env : Finite.Assignment n),
    env ∈ AssignmentSearch.assignments n
  | 0, env => by
    apply List.mem_singleton.mpr
    funext i
    exact i.elim0
  | n + 1, env => by
    have push : env.tail.push (env 0) = env := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    have tailMem := assignment_mem env.tail
    simp only [AssignmentSearch.assignments, List.mem_append, List.mem_map]
    cases h : env 0 with
    | false => exact Or.inl ⟨env.tail, tailMem, h ▸ push⟩
    | true => exact Or.inr ⟨env.tail, tailMem, h ▸ push⟩

theorem trace_agrees_of_no_difference {L : List (Ty Empty)} {n : Nat} (p q : Finite.Normal L n)
    (h : AssignmentSearch.normalDifference? p q = none) (env : Finite.Assignment n) :
    p.traceTree env = q.traceTree env := by
  unfold AssignmentSearch.normalDifference? at h
  have atEnv := List.findSome?_eq_none_iff.mp h env (assignment_mem env)
  split at atEnv
  · contradiction
  · exact Classical.not_not.mp ‹_›

theorem compareSelected_ne_unknown {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L)
    (hp : (admitSelected? p).isSome) (hq : (admitSelected? q).isSome) :
    compareSelected p q ≠ .unknown := by
  obtain ⟨left, hl⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨right, hr⟩ := Option.isSome_iff_exists.mp hq
  unfold compareSelected
  split
  · intro impossible
    cases impossible
  · rename_i oldUnknown
    simp only [hl, hr, Id.run, pure]
    split
    · intro impossible
      cases impossible
    · rename_i noWitness
      have noDifference : AssignmentSearch.difference? left.tree right.tree = none := by
        cases h : AssignmentSearch.difference? left.tree right.tree with
        | none => rfl
        | some input => exact False.elim (noWitness input h)
      have modelAgrees env :=
        congrArg (Reply.Normal.outcomesWith (Reply.Exits.Exit.packed (L := L)))
          (trace_agrees_of_no_difference left.tree.normal right.tree.normal noDifference env)
      have same := eq_of_observations left.tree right.tree (fun env =>
        (left.tree.map_outcomes env).trans ((modelAgrees env).trans (right.tree.map_outcomes env).symm))
      have compareComplete := projection_compare_iff p q left.tree right.tree left.target_eq right.target_eq
      have packedEq := left.packed_eq.trans
        ((congrArg (fun x => x.target.packed) same).trans right.packed_eq.symm)
      have accepted := compareComplete.mpr packedEq
      rw [oldUnknown] at accepted
      contradiction

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveAdmission
