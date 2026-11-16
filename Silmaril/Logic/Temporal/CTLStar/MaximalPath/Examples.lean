module

public import Silmaril.Logic.Temporal.CTLStar.MaximalPath.Thms
public import Silmaril.Logic.Temporal.CTLStar.FiniteScalar.Examples
public import Silmaril.Logic.Temporal.CTLStar.InfiniteBridge.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.MaximalPath.Examples
abbrev singleton := FiniteScalar.Examples.singleton
abbrev loop := InfiniteBridge.Examples.loop
abbrev chain := FiniteScalar.Examples.chain

/-- A finite zero-edge path suffices, despite there being no infinite witness. -/
theorem singleton_weakNext : ModalMu.Sat singleton (formula (.weakNext .bot) ()) := by
  change _ ∨ _
  exact Or.inl FiniteScalar.Examples.singleton_weakNext

theorem singleton_strongNext : ¬ ModalMu.Sat singleton (formula (.strongNext .top) ()) := by
  intro h
  obtain ⟨path, _, hp⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
  exact path.edges 0 hp.1

/-- An infinite witness suffices, despite there being no finite maximal path. -/
theorem loop_true : ModalMu.Sat loop (formula .top ()) := by
  change _ ∨ _
  exact Or.inr InfiniteBridge.Examples.loop_true_accepts

theorem loop_has_no_finite_witness : ¬ ModalMu.Sat loop (FiniteScalar.formula .top ()) :=
  FiniteScalar.Examples.cycle_no_finite_path

/-- Neither lifetime can repair a genuinely false Until obligation. -/
theorem postponed_until {S : ModalMu.Signature} (M : ModalMu.Model S) (a : S.Action) :
    ¬ ModalMu.Sat M (formula (.until .top .bot) a) := by
  intro h
  obtain ⟨path, _, d, _, hd, _⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
  exact hd

theorem singleton_release : ModalMu.Sat singleton (formula (.release .bot .top) ()) := by
  change _ ∨ _
  exact Or.inl FiniteScalar.Examples.singleton_finiteRelease

theorem loop_release : ModalMu.Sat loop (formula (.release .bot .top) ()) := by
  apply (formula_iff_accepts _ _ _ ModalMu.emptyEnv _).mpr
  apply Or.inr
  refine ⟨fun _ => (), ⟨rfl, fun _ => trivial⟩, ?_⟩
  exact InfiniteBridge.Examples.release_forever_accepts _

theorem one_edge_next : ModalMu.Sat chain (formula (.strongNext (.pos ())) ()) := by
  change _ ∨ _
  exact Or.inl FiniteScalar.Examples.one_edge_next

theorem one_edge_two_next : ¬ ModalMu.Sat chain (formula (.strongNext (.strongNext .top)) ()) := by
  intro h
  obtain ⟨path, _, hp⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
  have h0 := path.edges 0 hp.1
  have h1 := path.edges 1 hp.2.1
  exact Bool.noConfusion (h0.2.symm.trans h1.1)

def sig : ModalMu.Signature := ⟨Bool, Unit⟩

/-- Initial choice between a p-only deadlock and a q-only infinite loop. -/
def mixed : ModalMu.Model sig where
  World := Option Bool
  step _ w v := (w = none ∧ ∃ b, v = some b) ∨ (w = some true ∧ v = some true)
  valuation b := {w | w = some b}
  point := none

def finitePath : CTLStar.Path (mixed.step ()) where
  state t := if t = 0 then none else some false
  last := some 1
  edges := by
    intro i hi
    change i+1 ≤ 1 at hi
    have hz : i = 0 := by omega
    subst i
    exact Or.inl ⟨rfl, false, rfl⟩
  terminal := by
    intro n hn v hv
    have hn' : n = 1 := (Option.some.inj hn).symm
    subst n
    rcases hv with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h

def infinitePath : CTLStar.Path (mixed.step ()) where
  state t := if t = 0 then none else some true
  last := none
  edges := by
    intro i _
    by_cases hi : i = 0
    · subst i
      exact Or.inl ⟨rfl, true, rfl⟩
    · exact Or.inr ⟨by simp [hi], by simp⟩
  terminal := by intro n hn; cases hn

/-- Finite and infinite branches may separately witness their own path formula. -/
theorem mixed_each (b : Bool) : ModalMu.Sat mixed (formula (.strongNext (.pos b)) ()) := by
  apply (formula_correct _ _ _ ModalMu.emptyEnv _).mpr
  cases b
  · exact ⟨finitePath, rfl, by change 1 ≤ 1; omega, rfl⟩
  · exact ⟨infinitePath, rfl, trivial, rfl⟩

/-- Cross-lifetime branches cannot be combined into one satisfying path. -/
theorem mixed_collision :
    ¬ ModalMu.Sat mixed
      (formula (.conj (.strongNext (.pos false)) (.strongNext (.pos true))) ()) := by
  intro h
  obtain ⟨path, _, hp⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
  have hf : path.state 1 = some false := hp.1.2
  have ht : path.state 1 = some true := hp.2.2
  cases hf.symm.trans ht

theorem source_timing :
    ¬ ModalMu.Sat mixed (formula (.conj (.pos true) (.strongNext (.pos true))) ()) := by
  intro h
  obtain ⟨path, h0, hp⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
  have hs : path.state 0 = some true := hp.1
  cases h0.symm.trans hs

theorem atom_collapse :
    ¬ ModalMu.Sat singleton
      (formula ((.conj (.pos true) (.neg false) : NNF.Formula Bool).map (fun _ => ())) ()) := by
  intro h
  obtain ⟨path, _, hp⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
  exact hp.2 hp.1

end Silmaril.Logic.Temporal.CTLStar.MaximalPath.Examples
