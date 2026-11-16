module

public import Silmaril.Logic.Temporal.CTLStar.UniversalPath.Thms
public import Silmaril.Logic.Temporal.CTLStar.MaximalPath.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.UniversalPath.Examples
abbrev singleton := MaximalPath.Examples.singleton
abbrev loop := MaximalPath.Examples.loop
abbrev mixed := MaximalPath.Examples.mixed

/-- The finite zero-edge maximal path makes weak next vacuously true. -/
theorem singleton_weakNext : ModalMu.Sat singleton (allFormula (.weakNext .bot) ()) := by
  apply (formula_correct _ _ _ ModalMu.emptyEnv _).mpr
  intro path _ hv
  exact path.edges 0 hv

/-- Deadlocks do have a zero-edge maximal path, so strong next is false. -/
theorem singleton_strongNext : ¬ ModalMu.Sat singleton (allFormula (.strongNext .top) ()) := by
  intro h
  have hn := (formula_iff_all _ _ _ ModalMu.emptyEnv _).mp h
  exact hn ((MaximalPath.formula_iff_accepts _ _ _ ModalMu.emptyEnv _).mp
    MaximalPath.Examples.singleton_weakNext)

theorem loop_strongNext : ModalMu.Sat loop (allFormula (.strongNext .top) ()) := by
  apply (formula_correct _ _ _ ModalMu.emptyEnv _).mpr
  intro path _
  refine ⟨?_, trivial⟩
  cases hl : path.last with
  | none => simp only [ValidIndex]
  | some n => exact False.elim (path.terminal n hl () trivial)

theorem loop_until : ¬ ModalMu.Sat loop (allFormula (.until .top .bot) ()) := by
  intro h
  let path : CTLStar.Path (loop.step ()) := {
    state := fun _ => ()
    last := none
    edges := fun _ _ => trivial
    terminal := by intro n hn; cases hn }
  obtain ⟨d, _, hd, _⟩ := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h path rfl
  exact hd

/-- A separate existential witness for each atom does not make either universal. -/
theorem mixed_exists_each (b : Bool) : ModalMu.Sat mixed (MaximalPath.formula (.strongNext (.pos b)) ()) :=
  MaximalPath.Examples.mixed_each b

theorem mixed_not_all_false : ¬ ModalMu.Sat mixed (allFormula (.strongNext (.pos false)) ()) := by
  intro h
  have hp := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
    MaximalPath.Examples.infinitePath rfl
  have hb : (some true : Option Bool) = some false := hp.2
  cases hb

theorem mixed_not_all_true : ¬ ModalMu.Sat mixed (allFormula (.strongNext (.pos true)) ()) := by
  intro h
  have hp := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
    MaximalPath.Examples.finitePath rfl
  have hb : (some false : Option Bool) = some true := hp.2
  cases hb

/-- Every maximal mixed path takes one real successor carrying one atom. -/
theorem mixed_all_disjunction :
    ModalMu.Sat mixed (allFormula (.strongNext (.disj (.pos false) (.pos true))) ()) := by
  apply (formula_correct _ _ _ ModalMu.emptyEnv _).mpr
  intro path h0
  have hv : path.Valid 1 := by
    cases hl : path.last with
    | none => simp only [Path.Valid, hl, ValidIndex]
    | some n =>
      show ValidIndex path.last 1
      rw [hl]
      change 1 ≤ n
      by_contra hn
      have hz : n = 0 := by omega
      subst n
      apply path.terminal 0 hl (some false)
      rw [h0]
      exact Or.inl ⟨rfl, false, rfl⟩
  refine ⟨hv, ?_⟩
  have edge : mixed.step () mixed.point (path.state 1) := by
    simpa only [h0] using path.edges 0 hv
  rcases edge with ⟨_, b, hb⟩ | ⟨hb, _⟩
  · cases b
    · exact Or.inl hb
    · exact Or.inr hb
  · cases hb

theorem mixed_not_all_conjunction :
    ¬ ModalMu.Sat mixed (allFormula (.strongNext (.conj (.pos false) (.pos true))) ()) := by
  intro h
  have hp := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
    MaximalPath.Examples.finitePath rfl
  have hb : (some false : Option Bool) = some true := hp.2.2
  cases hb

/-- Both finite and infinite witness lifetimes satisfy Release forever/through endpoint. -/
theorem mixed_release : ModalMu.Sat mixed (allFormula (.release .bot .top) ()) := by
  apply (formula_correct _ _ _ ModalMu.emptyEnv _).mpr
  intro path _ d _
  exact Or.inl trivial

theorem source_timing : ¬ ModalMu.Sat mixed (allFormula (.pos true) ()) := by
  intro h
  have hp := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
    MaximalPath.Examples.finitePath rfl
  have hb : (none : Option Bool) = some true := hp
  cases hb

theorem atom_collapse :
    ¬ ModalMu.Sat mixed
      (allFormula ((.disj (.pos true) (.neg false) : NNF.Formula Bool).dual.map (fun _ => true)) ()) := by
  intro h
  have hp := (formula_correct _ _ _ ModalMu.emptyEnv _).mp h
    MaximalPath.Examples.finitePath rfl
  exact hp.1 hp.2

end Silmaril.Logic.Temporal.CTLStar.UniversalPath.Examples
