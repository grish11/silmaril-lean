module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Proofs

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}

theorem keepsAll (ops : List (Operation args)) : DeletesStores 0 ops ops := by
  induction ops with
  | nil => exact .nil
  | cons op _ ih => exact .keep op ih

theorem compose {removed more : Nat} {source middle target : List (Operation args)}
    (first : DeletesStores removed source middle) (next : DeletesStores more middle target) :
    DeletesStores (removed + more) source target := by
  induction first generalizing more target with
  | nil => simpa only [Nat.zero_add] using next
  | keep op _ ih =>
    cases next with
    | keep _ rest => exact .keep op (ih rest)
    | drop address value rest => simpa only [Nat.add_succ] using DeletesStores.drop address value (ih rest)
  | drop address value _ ih =>
    simpa only [Nat.succ_add] using DeletesStores.drop address value (ih next)

private def countStores : List (Operation args) → Nat
  | [] => 0
  | .store _ _ :: rest => countStores rest + 1
  | .load _ :: rest | .ret _ :: rest => countStores rest

private theorem countStores_operations {past : List (List ValueSort)} {version : Nat}
    (body : Body args past version) : countStores (operations body) = storeCount body := by
  induction body with
  | ret => rfl
  | load _ _ _ ih => exact ih
  | store _ _ _ _ ih => exact congrArg (· + 1) ih

private theorem countStores_deletes {removed : Nat} {source target : List (Operation args)}
    (deletes : DeletesStores removed source target) :
    countStores target + removed = countStores source := by
  induction deletes with
  | nil => rfl
  | keep op _ ih => cases op <;> simp only [countStores] <;> omega
  | drop _ _ _ ih => simp only [countStores]; omega

theorem deletes_storeCount {graph rewritten : Graph args} {removed : Nat}
    (deletes : DeletesStores removed (operations graph) (operations rewritten)) :
    storeCount rewritten + removed = storeCount graph := by
  simpa only [countStores_operations] using countStores_deletes deletes

theorem reindex_operations {past : List (List ValueSort)} {version : Nat}
    (body : Body args past version) (live : Nat) :
    operations (reindexMemory body live) = operations body := by
  induction body generalizing live <;> simp [reindexMemory, operations, *]

private theorem rewriteAt_deletes {past : List (List ValueSort)} {version : Nat}
    {candidate : Candidate} {facts : Certificate args} (body rewritten : Body args past version)
    (success : rewriteAt candidate facts body = some rewritten) :
    DeletesStores 1 (operations body) (operations rewritten) := by
  induction body with
  | ret => cases success
  | load _ address _ ih =>
    obtain ⟨tail, accepted, rfl⟩ := Option.map_eq_some_iff.mp success
    exact .keep (.load address) (ih tail accepted)
  | @store _ version _ address value rest ih =>
    by_cases hit : version + 1 = candidate.removeVersion
    · simp only [rewriteAt, ite_eq_left hit] at success
      split at success
      · have same := Option.some.inj success
        subst rewritten
        rw [reindex_operations]
        exact .drop address value (keepsAll (operations rest))
      · cases success
    · simp only [rewriteAt, ite_eq_right hit] at success
      obtain ⟨tail, accepted, rfl⟩ := Option.map_eq_some_iff.mp success
      exact .keep (.store address value) (ih tail accepted)

theorem checked_operations {graph rewritten : Graph args} {candidate : Candidate} {facts : Certificate args}
    (input : Tuple (Val cells) args) (accepted : Memory.DeadStore.rewrite graph candidate facts input = some rewritten) :
    DeletesStores 1 (operations graph) (operations rewritten) :=
  rewriteAt_deletes graph rewritten ((Memory.DeadStore.rewrite_eq_some_iff input).mp accepted).1

private theorem step_deletes {graph : Graph args} {step : Selection.Result args}
    {input : Tuple (Val cells) args} (success : Readers.rewrite graph input = some step) :
    DeletesStores 1 (operations graph) (operations step.graph) :=
  checked_operations input (Readers.rewrite_checked input success).2.2.2

theorem run_preserves (input : Tuple (Val cells) args) (fuel : Nat) (graph : Graph args) :
    let result := run input fuel graph
    DeletesStores result.deleted (operations graph) (operations result.graph) ∧
      ∀ initial : Heap cells, result.graph.denote input initial = graph.denote input initial := by
  induction fuel generalizing graph with
  | zero => exact ⟨keepsAll _, fun _ => rfl⟩
  | succ fuel ih =>
    simp only [run]
    split
    · exact ⟨keepsAll _, fun _ => rfl⟩
    next step success =>
      obtain ⟨deletes, denote⟩ := ih step.graph
      exact ⟨Nat.add_comm 1 _ ▸ compose (step_deletes success) deletes,
        fun initial => (denote initial).trans (Readers.rewrite_denote input success initial)⟩

theorem run_exhausted (input : Tuple (Val cells) args) (fuel : Nat) (graph : Graph args)
    (bound : storeCount graph ≤ fuel) : Readers.rewrite (run input fuel graph).graph input = none := by
  induction fuel generalizing graph with
  | zero =>
    change Readers.rewrite graph input = none
    cases success : Readers.rewrite graph input with
    | none => rfl
    | some step =>
      have count := deletes_storeCount (step_deletes success)
      omega
  | succ fuel ih =>
    simp only [run]
    split
    next success => exact success
    next step success =>
      have count := deletes_storeCount (step_deletes success)
      exact ih step.graph (by omega)

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Proofs
