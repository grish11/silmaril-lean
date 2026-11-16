module

public import Silmaril.Logic.Temporal.CTLStar.FiniteScalar.Thms
public import Silmaril.Logic.Temporal.FiniteAutomaton.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.FiniteScalar.Examples
open ModalMu
abbrev singleton := FiniteAutomaton.Examples.singleton
abbrev chain := FiniteAutomaton.Examples.chain
abbrev loop := FiniteAutomaton.Examples.loop
abbrev branch := FiniteAutomaton.Examples.branch

/-- A deadlocked singleton is a finite path of zero edges. -/
theorem singleton_weakNext : ModalMu.Sat singleton (formula (.weakNext .bot) ()) := by
  apply (formula_correct _ _ _ emptyEnv _).mpr
  refine ⟨0, fun _ => (), rfl, ?_, fun _ h => h, ?_⟩
  · intro i hi; omega
  · exact NNF.Formula.weakNext_at_last _ _ _

theorem singleton_strongNext : ¬ ModalMu.Sat singleton (formula (.strongNext .top) ()) := by
  intro h
  obtain ⟨n, path, _, edges, _, hp⟩ := (formula_correct _ _ _ emptyEnv _).mp h
  rcases n with _ | n
  · exact NNF.Formula.strongNext_at_last _ _ _ hp
  · exact edges 0 (Nat.zero_lt_succ n)

theorem singleton_postponedUntil : ¬ ModalMu.Sat singleton (formula (.until .top .bot) ()) := by
  intro h
  obtain ⟨n, path, _, edges, _, hp⟩ := (formula_correct _ _ _ emptyEnv _).mp h
  rcases n with _ | n
  · exact (NNF.Formula.until_at_last _ _ _ 0).mp hp
  · exact edges 0 (Nat.zero_lt_succ n)

theorem singleton_finiteRelease : ModalMu.Sat singleton (formula (.release .bot .top) ()) := by
  apply (formula_correct _ _ _ emptyEnv _).mpr
  refine ⟨0, fun _ => (), rfl, ?_, fun _ h => h, ?_⟩
  · intro i hi; omega
  · exact (NNF.Formula.release_at_last _ _ _ 0).mpr trivial

/-- The one edge reads its source before consuming the successor letter. -/
theorem one_edge_next : ModalMu.Sat chain (formula (.strongNext (.pos ())) ()) := by
  apply (formula_correct _ _ _ emptyEnv _).mpr
  refine ⟨1, fun t => if t = 0 then false else true, rfl, ?_, ?_, ?_⟩
  · intro i hi
    have hz : i = 0 := by omega
    subst i
    exact ⟨rfl, rfl⟩
  · intro v hv
    exact Bool.noConfusion hv.1
  · exact ⟨Nat.le_refl 1, rfl⟩

theorem one_edge_two_next : ¬ ModalMu.Sat chain (formula (.strongNext (.strongNext .top)) ()) := by
  intro h
  obtain ⟨n, path, _, edges, _, hp⟩ := (formula_correct _ _ _ emptyEnv _).mp h
  have hn : 2 ≤ n := hp.2.1
  have h0 := edges 0 (by omega)
  have h1 := edges 1 (by omega)
  exact Bool.noConfusion (h0.2.symm.trans h1.1)

theorem source_guard_timing : ¬ ModalMu.Sat chain (formula (.conj (.pos ()) (.strongNext (.pos ()))) ()) := by
  intro h
  obtain ⟨n, path, h0, _, _, hp⟩ := (formula_correct _ _ _ emptyEnv _).mp h
  have hs : path 0 = true := hp.1
  exact Bool.noConfusion (h0.symm.trans hs)

/-- A true endpoint cannot authorize stopping on a cycle. -/
theorem cycle_no_finite_path : ¬ ModalMu.Sat loop (formula .top ()) := by
  intro h
  obtain ⟨n, path, _, _, hd, _⟩ := (formula_correct _ _ _ emptyEnv _).mp h
  exact hd () trivial

/-- Each individual leaf has a coherent finite witnessing branch. -/
theorem branch_each (b : Bool) : ModalMu.Sat branch (formula (.strongNext (.pos b)) ()) := by
  apply (formula_correct _ _ _ emptyEnv _).mpr
  refine ⟨1, fun t => if t = 0 then none else some b, rfl, ?_, ?_, ?_⟩
  · intro i hi
    have hz : i = 0 := by omega
    subst i
    exact ⟨rfl, b, rfl⟩
  · intro v hv
    cases hv.1
  · exact ⟨Nat.le_refl 1, rfl⟩

/-- Two successor constraints cannot borrow different source branches. -/
theorem branch_collision :
    ¬ ModalMu.Sat branch (formula (.conj (.strongNext (.pos false)) (.strongNext (.pos true))) ()) := by
  intro h
  obtain ⟨n, path, _, _, _, hp⟩ := (formula_correct _ _ _ emptyEnv _).mp h
  have hf : path 1 = some false := hp.1.2
  have ht : path 1 = some true := hp.2.2
  cases hf.symm.trans ht

/-- Noninjective atom maps preserve the actual syntactic compiler theorem. -/
def distinct : NNF.Formula Bool := .conj (.pos true) (.neg false)

theorem atom_collapse :
    ¬ ModalMu.Sat singleton (formula (distinct.map (fun _ => ())) ()) := by
  intro h
  obtain ⟨n, path, _, _, _, hp⟩ := (formula_correct _ _ _ emptyEnv _).mp h
  exact hp.2 hp.1

end Silmaril.Logic.Temporal.CTLStar.FiniteScalar.Examples
