module

public import Silmaril.Logic.SetTheory.Universes.Finite.Defs
public import Silmaril.Logic.SetTheory.Universes.Thms

@[expose] public section

namespace Silmaril.Logic.SetTheory

universe u v

open ZFSet

namespace FiniteTower

/-- The empty universe supply requires no set-theoretic assumptions. -/
def empty : FiniteTower.{u} 0 where
  U := fun _ => ∅
  isGrothendieck _ hi := (Nat.not_lt_zero _ hi).elim
  mem_succ _ hi := (Nat.not_lt_zero _ hi).elim

/-- Discard the upper part of a finite tower. -/
def restrict {m n : ℕ} (T : FiniteTower.{u} n) (hmn : m ≤ n) : FiniteTower.{u} m where
  U := T.U
  isGrothendieck i hi := T.isGrothendieck i (hi.trans_le hmn)
  mem_succ i hi := T.mem_succ i (hi.trans_le hmn)

/-- A finite tower embeds in any larger Lean set carrier. -/
noncomputable def lift {n : ℕ} (T : FiniteTower.{u} n) : FiniteTower.{max u v} n where
  U := fun i => liftSet.{u, v} (T.U i)
  isGrothendieck i hi := (T.isGrothendieck i hi).liftSet
  mem_succ i hi := liftSet_mem_liftSet (T.mem_succ i hi)

/-- Add one universe by moving to the next Lean carrier and appending all lower sets. -/
noncomputable def raise {n : ℕ} (T : FiniteTower.{u} n) : FiniteTower.{u + 1} (n + 1) where
  U := fun i => if i < n then liftSet.{u, u + 1} (T.U i) else universeSet.{u}
  isGrothendieck i _ := by
    split_ifs with hi
    · exact (T.isGrothendieck i hi).liftSet
    · exact isGrothendieckUniverse_universeSet
  mem_succ i hi := by
    have hin : i < n := by omega
    simp only [ite_eq_left hin]
    by_cases hs : i + 1 < n
    · simp only [ite_eq_left hs]
      exact liftSet_mem_liftSet (T.mem_succ i hs)
    · simp only [ite_eq_right hs]
      exact liftSet_mem_universeSet (T.U i)

/-- The levels are cumulative within their common finite bound. -/
theorem mono {n : ℕ} (T : FiniteTower.{u} n) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    T.U i ⊆ T.U j := by
  induction hij with
  | refl => exact fun _ h => h
  | @step j hij ih =>
    have hjn : j < n := by omega
    exact (fun _ hx => (T.isGrothendieck (j + 1) hj).isTransitive
      (T.U j) (T.mem_succ j hj) (ih hjn hx))

/-- Any lower level belongs to any strictly higher in-range level. -/
theorem mem_of_lt {n : ℕ} (T : FiniteTower.{u} n) {i j : ℕ} (hij : i < j) (hj : j < n) :
    T.U i ∈ T.U j := by
  have hs : i + 1 < n := by omega
  exact T.mono (by omega : i + 1 ≤ j) hj (T.mem_succ i hs)

/-- One Grothendieck universe in the next Lean carrier. -/
noncomputable def one : FiniteTower.{u + 1} 1 := empty.{u}.raise

/-- Two nested Grothendieck universes in two successively larger Lean carriers. -/
noncomputable def two : FiniteTower.{u + 2} 2 := one.{u}.raise

/-- Three nested Grothendieck universes in three successively larger Lean carriers. -/
noncomputable def three : FiniteTower.{u + 3} 3 := two.{u}.raise

end FiniteTower

/-- No universe supply is needed for the empty bound. -/
instance hasFiniteTowerZero : HasFiniteTower.{u} 0 := ⟨⟨FiniteTower.empty⟩⟩

/-- First concrete engineering-induction instance. -/
instance hasFiniteTowerOne : HasFiniteTower.{u + 1} 1 := ⟨⟨FiniteTower.one⟩⟩

/-- Second concrete engineering-induction instance. -/
instance hasFiniteTowerTwo : HasFiniteTower.{u + 2} 2 := ⟨⟨FiniteTower.two⟩⟩

/-- Third concrete engineering-induction instance. -/
instance hasFiniteTowerThree : HasFiniteTower.{u + 3} 3 := ⟨⟨FiniteTower.three⟩⟩

end Silmaril.Logic.SetTheory
