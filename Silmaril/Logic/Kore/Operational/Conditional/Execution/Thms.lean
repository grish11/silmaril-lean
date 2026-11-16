module

public import Silmaril.Logic.Kore.Operational.Conditional.Execution.Defs
import Silmaril.Proofs.Logic.Kore.Operational.Conditional.Execution

@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Conditional.Execution

theorem fire_iff (r : Rule) (c d : Config) :
    fire r c = some d ↔ ∃ v : Valuation,
      v.x = v.capturedVal ∧ r.guard.Holds v.x ∧
      c = r.beforeConfig v ∧ d = r.afterConfig v :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Execution.fire_iff r c d

/-- Exact completeness and soundness for every installed rule, not first-match execution. -/
theorem mem_successors (rules : List Rule) (c d : Config) :
    d ∈ successors rules c ↔ Step rules c d :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Execution.mem_successors rules c d

theorem successors_nil_iff (rules : List Rule) (c : Config) :
    successors rules c = [] ↔ ∀ d, ¬ Step rules c d :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Execution.successors_nil_iff rules c

/-- Exactly n transitions, with no deadlock stuttering. -/
theorem mem_frontier (rules : List Rule) (n : Nat) (c d : Config) :
    d ∈ frontier rules n c ↔ Runs rules n c d :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Execution.mem_frontier rules n c d

/-- At most n transitions, explicitly distinct from the exact frontier. -/
theorem mem_explore (rules : List Rule) (n : Nat) (c d : Config) :
    d ∈ explore rules n c ↔ ∃ k, k ≤ n ∧ Runs rules k c d :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Execution.mem_explore rules n c d

/-- Existing finite reachability is precisely eventual finite-search membership.
Failure at one finite bound supplies no unbounded unreachability result. -/
theorem reaches_iff_explore (rules : List Rule) (c d : Config) :
    Reachability.Reaches (Step rules) (fun e => e = d) c ↔
      ∃ n, d ∈ explore rules n c :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Execution.reaches_iff_explore rules c d

/-- The existing source rule's finite-reachability contract has an exact search
interpretation for every coherent enabled capture. No bound is claimed uniform. -/
theorem compile_satisfies_iff_explore (rules : List Rule) (r : Rule) :
    r.compile.Satisfies KSort.config (model (Step rules)) ↔
      ∀ v, v.x = v.capturedVal → r.guard.Holds v.x →
        ∃ n, r.afterConfig v ∈ explore rules n (r.beforeConfig v) := by
  rw [compile_satisfies_iff]
  simp_rw [reaches_iff_explore]

/-- Search after complete text checking uses only installed axioms; checked claims
remain goals and supply no executable transitions. -/
theorem checked_successors_iff {input : String} {p : CheckedProgram}
    (_h : check input = some p) (c d : Config) :
    d ∈ successors p.axioms c ↔ Step p.axioms c d :=
  mem_successors p.axioms c d

/-- Exact checked-text result, retaining successor order and multiplicity. -/
theorem successors?_of_check {input : String} {p : CheckedProgram}
    (h : check input = some p) (c : Config) :
    successors? input c = some (successors p.axioms c) := by
  simp [successors?, h]

/-- Successful execution identifies an actual completely checked source, with
the exact output list, not just its set of endpoints. -/
theorem successors?_some_iff (input : String) (c : Config) (ds : List Config) :
    successors? input c = some ds ↔
      ∃ p, check input = some p ∧ ds = successors p.axioms c := by
  cases h : check input with
  | none => simp [successors?, h]
  | some p => simp [successors?, h, eq_comm]

/-- Malformed or unsupported text rejects; an accepted empty successor list is
a distinct outcome. This does not assert frontend completeness. -/
theorem successors?_none_iff (input : String) (c : Config) :
    successors? input c = none ↔ check input = none := by
  cases h : check input with
  | none => simp [successors?, h]
  | some p => simp [successors?, h]

/-- Every and only source step is present after successful text checking. -/
theorem successors?_mem_iff {input : String} {p : CheckedProgram}
    (h : check input = some p) (c d : Config) :
    (∃ ds, successors? input c = some ds ∧ d ∈ ds) ↔ Step p.axioms c d := by
  rw [successors?_of_check h]
  constructor
  · rintro ⟨ds, hds, hd⟩
    have hs : successors p.axioms c = ds := Option.some.inj hds
    subst ds
    exact (mem_successors p.axioms c d).1 hd
  · intro hd
    exact ⟨_, rfl, (mem_successors p.axioms c d).2 hd⟩

end Silmaril.Logic.Kore.Operational.Conditional.Execution
