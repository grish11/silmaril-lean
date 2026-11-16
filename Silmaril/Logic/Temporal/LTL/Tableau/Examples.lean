module

public import Silmaril.Logic.Temporal.LTL.Tableau.Modal
public import Silmaril.Logic.Temporal.LTL.NNF.Examples

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.LTL.Tableau.Examples
open Buchi.Automaton

theorem nested_accepted :
    (automaton (NNF.normalize false NNF.Examples.nested)).Accepts (fun _ a => a = true) :=
  (accepts_iff _ _).mpr (NNF.Examples.nested_accepted 0)

theorem nested_rejected :
    ¬ (automaton (NNF.normalize false NNF.Examples.nested)).Accepts NNF.Examples.constantWord :=
  fun h => NNF.Examples.nested_rejected 0 ((accepts_iff _ _).mp h)

/-- The local until equation alone permits the false postponing solution. -/
def postponing : State (shape (NNF.Formula.until (.top : NNF.Formula Unit) .bot)) :=
  Sum.elim (fun _ => true) (Sum.elim (fun _ => true) (fun _ => false))

theorem postponing_local (letter : Unit → Prop) :
    Local (.until .top .bot) letter postponing postponing := by
  simp [Local, postponing, bit, root, left, right]

theorem postponing_not_fair :
    ¬ Fair (.until .top .bot) (fun _ => postponing) := by
  intro h
  obtain ⟨u, _, hu⟩ := h (.inl ()) 0
  change true = false ∨ false = true at hu
  simp at hu

theorem postponed_until_rejected (word : Nat → Unit → Prop) :
    ¬ (automaton (.until .top .bot)).Accepts word := by
  intro h
  obtain ⟨d, hd, _⟩ := (accepts_iff _ _).mp h
  exact hd

/-- An inactive release may still be semantically true. This selected-bit
solution is locally consistent, but it is not an initial root-true witness. -/
def inactiveRelease : State (shape (NNF.Formula.release (.bot : NNF.Formula Unit) .top)) :=
  Sum.elim (fun _ => false) (Sum.elim (fun _ => false) (fun _ => true))

theorem release_inactive_local (letter : Unit → Prop) :
    Local (.release .bot .top) letter inactiveRelease inactiveRelease := by
  simp [Local, inactiveRelease, bit, root, left, right]

theorem release_inactive_but_true (word : Nat → Unit → Prop) (t : Nat) :
    bit inactiveRelease = false ∧ (NNF.Formula.release .bot .top).Holds word t :=
  ⟨rfl, NNF.Examples.release_forever word t⟩

theorem release_forever_accepted (word : Nat → Unit → Prop) :
    (automaton (.release .bot .top)).Accepts word :=
  (accepts_iff _ _).mpr (NNF.Examples.release_forever word 0)

/-- No until occurrence needs a nontrivial acceptance condition. -/
theorem next_only_accepted :
    (automaton (NNF.Formula.next (.pos ()))).Accepts (fun t _ => 0 < t) :=
  (accepts_iff _ _).mpr (by change 0 < 0+1; decide)

theorem inconsistent_atoms_rejected (word : Nat → Unit → Prop) :
    ¬ (automaton (.conj (.pos ()) (.neg ()))).Accepts word := by
  intro h
  have hc : word 0 () ∧ ¬ word 0 () := (accepts_iff _ _).mp h
  exact hc.2 hc.1

/-- Deadlocks have no infinite path; no implicit self-loop is inserted. -/
theorem deadlock {S : ModalMu.Signature} (p : LTL.Formula S.Atom) (a : S.Action)
    (M : ModalMu.Model S) (dead : ∀ v, ¬ M.step a M.point v) :
    ¬ ModalMu.Sat M (ltlFormula p a) := by
  intro h
  obtain ⟨path, ⟨h0, edges⟩, _⟩ := (ltlFormula_correct p a M ModalMu.emptyEnv M.point).mp h
  exact dead (path 1) (h0 ▸ edges 0)

def boolSignature : ModalMu.Signature := ⟨Bool, Unit⟩

/-- Every world has infinitely many successors; atom truth is constant in time. -/
def branchingModel : ModalMu.Model boolSignature where
  World := Nat
  step _ _ _ := True
  valuation a := {_w : Nat | a = true}
  point := 0

theorem infinitely_branching_nested : ModalMu.Sat branchingModel
    (ltlFormula NNF.Examples.nested ()) := by
  apply (ltlFormula_correct (S := boolSignature) NNF.Examples.nested () branchingModel
    ModalMu.emptyEnv branchingModel.point).mpr
  refine ⟨fun _ => branchingModel.point, ⟨rfl, fun _ => trivial⟩, ?_⟩
  exact (NNF.normalize_positive _ NNF.Examples.nested 0).mp (NNF.Examples.nested_accepted 0)

def unitSignature : ModalMu.Signature := ⟨Unit, Unit⟩

def sourceModel : ModalMu.Model unitSignature where
  World := Nat
  step _ w v := v = w+1
  valuation _ := {w | 0 < w}
  point := 0

/-- Atom truth at the successor does not repair the false initial source letter. -/
theorem source_timing_rejected :
    ¬ ModalMu.Sat sourceModel (ltlFormula (.atom ()) ()) := by
  intro h
  obtain ⟨path, ⟨h0, _⟩, hp⟩ := (ltlFormula_correct (S := unitSignature) (.atom ()) ()
    sourceModel ModalMu.emptyEnv sourceModel.point).mp h
  delta sourceModel at path h0 hp
  have hn : 0 < (path 0 : Nat) := hp
  change (path 0 : Nat) = 0 at h0
  rw [h0] at hn
  exact Nat.lt_irrefl 0 hn

/-- Distinct source atoms can satisfy a positive/negative pair. -/
theorem distinct_atoms_accepted :
    (automaton (.conj (.pos false) (.neg true))).Accepts (fun _ a => a = false) := by
  rw [accepts_iff]
  simp [NNF.Formula.Holds]

/-- Identifying the atoms creates a contradiction, while preserving shape. -/
theorem collapsed_atoms_rejected (word : Nat → Unit → Prop) :
    ¬ (automaton ((.conj (.pos false) (.neg true) : NNF.Formula Bool).map (fun _ => ()))).Accepts word := by
  rw [accepts_iff]
  simp [NNF.Formula.map, NNF.Formula.Holds]

end Silmaril.Logic.Temporal.LTL.Tableau.Examples
