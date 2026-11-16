module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Symbolic
public import Silmaril.Logic.Temporal.Buchi.Automaton.Modal
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace Silmaril.Logic.Temporal.Buchi.Automaton.Examples

/-- Both next states are available: rejecting choices do not invalidate the
existence of a different, accepting run. -/
def choose : Buchi.Automaton Unit 2 where
  initial := {0}
  step _ _ _ := True
  accepting := {1}

theorem nondeterministic_acceptance : choose.Accepts (fun _ => ()) := by
  refine ⟨fun k => if k = 0 then 0 else 1, by simp [choose], fun _ => trivial, ?_⟩
  intro k
  exact ⟨k+1, Nat.le_succ k, by simp [choose]⟩

theorem rejecting_run_also_exists :
    choose.IsRun (fun _ => ()) (fun _ => 0) ∧ ¬ choose.Recurrent (fun _ => 0) := by
  refine ⟨fun _ => trivial, ?_⟩
  rintro h
  obtain ⟨m, _, hm⟩ := h 0
  norm_num [choose] at hm

theorem nondeterministic_product :
    Buchi.Accepts (choose.productStep (fun (_ _ : Unit) => True) (fun _ => ()))
      choose.productAccepting ((), 0) := by
  apply (path_run_iff_product choose _ _ () 0).mp
  obtain ⟨r, h0, hr, hf⟩ := nondeterministic_acceptance
  exact ⟨fun _ => (), ⟨rfl, fun _ => trivial⟩, r, h0, hr, hf⟩

/-- Wait in 0, visit accepting 1 once, then remain in rejecting sink 2. -/
def oneVisit : Buchi.Automaton Unit 3 where
  initial := {0}
  step q _ r := q = 0 ∨ r = 2
  accepting := {1}

def delayedRun (delay k : Nat) : Fin 3 :=
  if k ≤ delay then 0 else if k = delay+1 then 1 else 2

theorem delayedRun_isRun (delay : Nat) :
    oneVisit.IsRun (fun _ => ()) (delayedRun delay) := by
  intro k
  change delayedRun delay k = 0 ∨ delayedRun delay (k+1) = 2
  by_cases h : k ≤ delay
  · exact Or.inl (by simp [delayedRun, h])
  · exact Or.inr (by simp only [delayedRun]; split_ifs <;> omega)

/-- Every requested late time has a complete initial run accepting then, but
the witnesses for different times cannot be exchanged for one recurrent run. -/
theorem arbitrarily_late_individual_visits :
    ∀ k, ∃ r : Nat → Fin 3, r 0 ∈ oneVisit.initial ∧
      oneVisit.IsRun (fun _ => ()) r ∧ ∃ m, k ≤ m ∧ r m ∈ oneVisit.accepting := by
  intro k
  exact ⟨delayedRun k, by simp [delayedRun, oneVisit], delayedRun_isRun k,
    k+1, Nat.le_succ k, by simp [delayedRun, oneVisit]⟩

theorem oneVisit_not_accepts : ¬ oneVisit.Accepts (fun _ => ()) := by
  rintro ⟨r, _, hr, hf⟩
  obtain ⟨m, _, hm⟩ := hf 0
  have hm1 : r m = 1 := hm
  have next : r (m+1) = 2 := by
    rcases hr m with h | h
    · rw [hm1] at h
      norm_num at h
    · exact h
  have sink : ∀ j, r (m+1+j) = 2 := by
    intro j
    induction j with
    | zero => simpa using next
    | succ j ih =>
      rcases hr (m+1+j) with h | h
      · rw [ih] at h
        norm_num at h
      · simpa [Nat.add_assoc] using h
  obtain ⟨k, hk, hacc⟩ := hf (m+1)
  have hs : r k = 2 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact sink j
  have ha : r k = 1 := hacc
  rw [hs] at ha
  norm_num at ha

theorem incoherent_product_rejected :
    ¬ oneVisit.AcceptsPath (fun (_ _ : Unit) => True) (fun _ => ()) () := by
  rintro ⟨p, _, h⟩
  exact oneVisit_not_accepts h

/-- A guard must hold at the source time; using the next label changes meaning. -/
def requiresTrue : Buchi.Automaton Prop 1 where
  initial := Set.univ
  step _ letter _ := letter
  accepting := Set.univ

theorem source_label_rejected :
    ¬ requiresTrue.AcceptsPath (fun (w v : Nat) => v = w+1) (fun w => 0 < w) 0 := by
  rintro ⟨p, ⟨h0, _⟩, r, _, hr, _⟩
  have h : 0 < p 0 := hr 0
  omega

theorem shifted_label_accepted :
    requiresTrue.AcceptsPath (fun (w v : Nat) => v = w+1) (fun w => 0 < w+1) 0 := by
  refine ⟨id, ⟨rfl, fun _ => rfl⟩, fun _ => 0, Set.mem_univ _, ?_, ?_⟩
  · intro k
    exact Nat.zero_lt_succ k
  · intro k
    exact ⟨k, le_rfl, Set.mem_univ _⟩

theorem accepting_deadlock_rejected :
    ¬ requiresTrue.AcceptsPath (fun (_ _ : Unit) => False) (fun _ => True) () :=
  not_acceptsPath_of_deadlock requiresTrue _ _ () (fun _ h => h)

theorem no_states_no_word (A : Buchi.Automaton Unit 0) (word : Word Unit) :
    ¬ A.Accepts word := by
  rintro ⟨r, _, _, _⟩
  exact Fin.elim0 (r 0)

def demoSignature : ModalMu.Signature := ⟨Unit, Unit⟩

/-- This frame has infinitely many successors at every state. -/
def branchingModel : ModalMu.Model demoSignature where
  World := Nat
  step _ _ _ := True
  valuation _ := Set.univ
  point := 0

def guardedChoice : Symbolic Unit 2 where
  initial := {0}
  guard _ _ := .pos ()
  accepting := {1}

theorem symbolic_infinite_branching : guardedChoice.AcceptsModel branchingModel () := by
  obtain ⟨r, hi, hr, hf⟩ := nondeterministic_acceptance
  refine ⟨fun _ => branchingModel.point, ⟨rfl, fun _ => trivial⟩, r, hi, ?_, hf⟩
  intro k
  exact Set.mem_univ _

theorem symbolic_product_fixedPoint : ∃ q ∈ guardedChoice.initial,
    (branchingModel.point, q) ∈ (Buchi.outer
      (guardedChoice.automaton.productStep (branchingModel.step ()) (modelLabel branchingModel))
      guardedChoice.automaton.productAccepting).gfp :=
  (Symbolic.acceptsModel_iff_gfp guardedChoice branchingModel ()).mp symbolic_infinite_branching

theorem symbolic_product_formula : ∃ q ∈ guardedChoice.initial,
    ModalMu.Sat (productModel guardedChoice.automaton (branchingModel.step ())
      (modelLabel branchingModel) branchingModel.point q) acceptingRunFormula :=
  (acceptsPath_iff_formula guardedChoice.automaton (branchingModel.step ())
    (modelLabel branchingModel) branchingModel.point).mp symbolic_infinite_branching

/-- A concrete compound guard compiles to ordinary positive modal μ syntax. -/
theorem compound_guard_syntax :
    ((Guard.conj (.pos ()) (.disj (.neg ()) .top)).toFormula :
      ModalMu.Formula demoSignature 3) = .conj (.pos ()) (.disj (.neg ()) .top) := rfl

end Silmaril.Logic.Temporal.Buchi.Automaton.Examples
