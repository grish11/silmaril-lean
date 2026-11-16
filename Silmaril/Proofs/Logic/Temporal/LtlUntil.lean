module

public import Silmaril.Logic.Temporal.LTL.Defs

@[expose] public section

namespace Silmaril.Logic.Temporal.LTL

theorem until_unfold_proof {P : Type} (M : Model P) (p q : Formula P) (n : Nat) :
    (Formula.until p q).Holds M n ↔
      q.Holds M n ∨ (p.Holds M n ∧ (Formula.until p q).Holds M (n + 1)) := by
  constructor
  · show (Formula.until p q).Holds M n →
      q.Holds M n ∨ (p.Holds M n ∧ (Formula.until p q).Holds M (n + 1))
    rintro ⟨d, hq, hp⟩
    cases d with
    | zero => exact Or.inl (by simpa only [Nat.add_zero] using hq)
    | succ d =>
      show q.Holds M n ∨ (p.Holds M n ∧ (Formula.until p q).Holds M (n + 1))
      refine Or.inr ⟨?_, d, ?_, ?_⟩
      · simpa only [Nat.add_zero] using hp 0 (Nat.zero_lt_succ d)
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
      · intro i hi
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hp (i + 1) (Nat.succ_lt_succ hi)
  · show q.Holds M n ∨ (p.Holds M n ∧ (Formula.until p q).Holds M (n + 1)) →
      (Formula.until p q).Holds M n
    rintro (hq | ⟨hp, d, hq, hs⟩)
    · exact ⟨0, by simpa only [Nat.add_zero] using hq,
        fun _ hi => False.elim (Nat.not_lt_zero _ hi)⟩
    · show (Formula.until p q).Holds M n
      refine ⟨d + 1, ?_, ?_⟩
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
      · intro i hi
        cases i with
        | zero => simpa only [Nat.add_zero] using hp
        | succ i =>
          simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hs i (Nat.lt_of_succ_lt_succ hi)

end Silmaril.Logic.Temporal.LTL
