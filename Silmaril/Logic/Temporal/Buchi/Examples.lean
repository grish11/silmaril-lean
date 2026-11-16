module

public import Silmaril.Logic.Temporal.Buchi.Modal

@[expose] public section
namespace Silmaril.Logic.Temporal.Buchi.Examples

/-- Infinite carrier, one genuine forward path, and infinitely many separated
accepting states rather than a finite or reflexive reachability surrogate. -/
theorem even_chain : Accepts (fun a b : Nat => b = a+1) {n | ∃ k, n = 2*k} 0 := by
  refine ⟨id, rfl, fun _ => rfl, ?_⟩
  intro n
  exact ⟨2*n, by omega, n, rfl⟩

/-- Being accepting at a deadlock cannot satisfy the νμ property. -/
theorem deadlock_rejected : ¬ Accepts (fun _ _ : Unit => False) Set.univ () := by
  rintro ⟨p, _, edges, _⟩
  exact edges 0

/-- A single accepting visit does not count as repeated acceptance. -/
theorem one_visit_rejected : ¬ Accepts (fun a b : Nat => b = a+1) {0} 0 := by
  rintro ⟨p, h0, edges, visits⟩
  have hp : ∀ n, p n = n := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => simpa [ih] using edges n
  obtain ⟨m, hm, hf⟩ := visits 1
  have hz : p m = 0 := hf
  rw [hp] at hz
  omega

/-- Empty carriers are admitted by the independent semantics. -/
theorem empty_no_start : ¬ ∃ w : Empty, Accepts (fun _ _ => True) Set.univ w := by
  rintro ⟨w, _⟩
  exact w.elim

/-- The actual nested fixed point inherits the deadlock exclusion. -/
theorem deadlock_fixed_point : () ∉ (outer (fun _ _ : Unit => False) Set.univ).gfp :=
  fun h => deadlock_rejected ((accepts_iff_gfp _ _ _).mpr h)

/-- Waiting keeps an accepting successor available, but taking it commits the
path to a nonaccepting trap. -/
def choiceStep (w v : Nat) : Prop :=
  (w = 0 ∧ (v = 0 ∨ v = 1)) ∨ (w = 1 ∧ v = 2) ∨ (w = 2 ∧ v = 2)

theorem recurring_opportunities :
    ∃ p : Nat → Nat, p 0 = 0 ∧ (∀ n, choiceStep (p n) (p (n+1))) ∧
      ∀ n, ∃ v, choiceStep (p n) v ∧ v ∈ ({1} : Set Nat) := by
  exact ⟨fun _ => 0, rfl, fun _ => Or.inl ⟨rfl, Or.inl rfl⟩,
    fun _ => ⟨1, Or.inl ⟨rfl, Or.inr rfl⟩, rfl⟩⟩

/-- Re-choosing a fresh branch for every eventuality is not Büchi acceptance. -/
theorem opportunities_not_accepting : ¬ Accepts choiceStep {1} 0 := by
  rintro ⟨p, _, edges, visits⟩
  obtain ⟨n, _, hn⟩ := visits 0
  have hfirst : p n = 1 := hn
  have enter : p (n+1) = 2 := by
    have h := edges n
    dsimp [choiceStep] at h
    omega
  have tail : ∀ k, p (n+1+k) = 2 := by
    intro k
    induction k with
    | zero => simpa using enter
    | succ k ih =>
        have h := edges (n+1+k)
        dsimp [choiceStep] at h
        have hs : p (n+1+k+1) = 2 := by omega
        simpa [Nat.add_assoc] using hs
  obtain ⟨m, hm, hf⟩ := visits (n+1)
  have ht := tail (m-(n+1))
  rw [Nat.add_sub_of_le hm] at ht
  have ha : p m = 1 := hf
  omega

def signature : ModalMu.Signature := ⟨Unit, Unit⟩

def evenChain : ModalMu.Model signature where
  World := Nat
  step _ a b := b = a+1
  valuation _ := {n | ∃ k, n = 2*k}
  point := 0

theorem native_even_chain : ModalMu.Sat evenChain (infinitelyOften () ()) :=
  (infinitelyOften_iff evenChain () () evenChain.point).mpr even_chain

def opportunities : ModalMu.Model signature where
  World := Nat
  step _ := choiceStep
  valuation _ := {1}
  point := 0

theorem native_opportunities_rejected : ¬ ModalMu.Sat opportunities (infinitelyOften () ()) :=
  fun h => opportunities_not_accepting ((infinitelyOften_iff opportunities () () opportunities.point).mp h)

/-- The entry has infinitely many distinct successors; each positive state
has a self-loop. No finite branching premise is needed by the theorem. -/
def hubStep (w v : Nat) : Prop := (w = 0 ∧ 0 < v) ∨ (0 < w ∧ v = w)

theorem infinite_branching : ∀ n, hubStep 0 (n+1) :=
  fun n => Or.inl ⟨rfl, Nat.zero_lt_succ n⟩

theorem hub_accepts : Accepts hubStep {1} 0 := by
  let p : Nat → Nat := fun n => if n = 0 then 0 else 1
  refine ⟨p, rfl, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact Or.inl ⟨rfl, Nat.zero_lt_one⟩
    | succ n => exact Or.inr ⟨Nat.zero_lt_one, rfl⟩
  · intro n
    exact ⟨n+1, Nat.le_succ n, rfl⟩

theorem hub_fixed_point : 0 ∈ (outer hubStep {1}).gfp :=
  (accepts_iff_gfp _ _ _).mp hub_accepts

end Silmaril.Logic.Temporal.Buchi.Examples
