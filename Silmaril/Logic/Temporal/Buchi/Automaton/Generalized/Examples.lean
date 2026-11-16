module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Generalized.Thms

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.Buchi.Automaton.Generalized.Examples

/-- Both fairness sets must be visited on one run. -/
def alternating : Symbolic Unit 2 2 where
  initial := Set.univ
  guard _ _ := .top
  accepting i := {i}

def alternatingRun (t : Nat) : Fin 2 := ⟨t % 2, Nat.mod_lt _ (by decide)⟩

theorem alternating_accepts (word : Nat → Unit → Prop) : alternating.Accepts word := by
  refine ⟨alternatingRun, Set.mem_univ _, fun _ => True.intro, ?_⟩
  intro i t
  refine ⟨2*t+i.val, by omega, ?_⟩
  change alternatingRun (2*t+i.val) = i
  apply Fin.ext
  change (2*t+i.val) % 2 = i.val
  have hi := i.isLt
  omega

theorem alternating_compiled (word : Nat → Unit → Prop) :
    alternating.compile.automaton.Accepts word :=
  (accepts_compile _ _).mpr (alternating_accepts word)

/-- Two absorbing branches: separate witnesses for separate requirements do
not combine into one accepting run. -/
def separated : Symbolic Unit 2 2 where
  initial := Set.univ
  guard q r := if q = r then .top else .bot
  accepting i := {i}

theorem individually_recurrent (i : Fin 2) (word : Nat → Unit → Prop) :
    ∃ r, r 0 ∈ separated.initial ∧ separated.IsRun word r ∧
      ∀ t, ∃ u, t ≤ u ∧ r u ∈ separated.accepting i := by
  refine ⟨fun _ => i, Set.mem_univ _, ?_, fun t => ⟨t, le_rfl, rfl⟩⟩
  intro t
  simp [separated, Guard.Holds]

theorem separated_rejects (word : Nat → Unit → Prop) : ¬ separated.Accepts word := by
  rintro ⟨r, _, hr, hf⟩
  have constant (t) : r t = r 0 := by
    induction t with
    | zero => rfl
    | succ t ih =>
      have h := hr t
      have he : r t = r (t+1) := by
        by_contra hn
        simp [separated, hn, Guard.Holds] at h
      exact he.symm.trans ih
  obtain ⟨u, _, hu⟩ := hf 0 0
  obtain ⟨v, _, hv⟩ := hf 1 0
  change r u = 0 at hu
  change r v = 1 at hv
  have he : (0 : Fin 2) = 1 := hu.symm.trans ((constant u).trans ((constant v).symm.trans hv))
  exact (by decide : (0 : Fin 2) ≠ 1) he

theorem separated_compiled_rejects (word : Nat → Unit → Prop) :
    ¬ separated.compile.automaton.Accepts word :=
  fun h => separated_rejects word ((accepts_compile _ _).mp h)

/-- With zero requirements an infinite valid self-loop is enough. -/
def noRequirements : Symbolic Unit 1 0 where
  initial := Set.univ
  guard _ _ := .top
  accepting := Fin.elim0

theorem zero_requirements_accept (word : Nat → Unit → Prop) :
    noRequirements.compile.automaton.Accepts word := by
  apply (accepts_compile _ _).mpr
  exact (accepts_zero _ _).mpr ⟨fun _ => 0, Set.mem_univ _, fun _ => True.intro⟩

/-- Even a sentinel-only monitor must read the original source guard. -/
def requiresSource : Symbolic Unit 1 0 where
  initial := Set.univ
  guard _ _ := .pos ()
  accepting := Fin.elim0

theorem source_label_rejected :
    ¬ requiresSource.compile.automaton.Accepts (fun t _ => 0 < t) := by
  intro h
  obtain ⟨r, _, hr, _⟩ := (accepts_compile _ _).mp h
  exact (Nat.lt_irrefl 0) (hr 0)

end Silmaril.Logic.Temporal.Buchi.Automaton.Generalized.Examples
