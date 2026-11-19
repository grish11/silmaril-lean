module

public import Silmaril.Logic.LinArith.Carrier.Thms

/-!
# Examples: Farkas certificates over WIT words

`x₀ ≤ 1` and `-x₀ ≤ -2` as `list<ineq>` (`sys`): the multipliers `[1, 1]` are accepted
(`sys_accepted`), so the system is in `Infeasible` (`sys_infeasible`); a negative multiplier,
a missing multiplier, and the satisfiable `x₀ ≤ 1, -x₀ ≤ 0` are rejected.
-/

@[expose] public section

namespace Silmaril.Logic.LinArith.Carrier.Examples

/-- `x₀ ≤ 1`, `-x₀ ≤ -2`. -/
def sys : SystemW := [⟨[(0, 1)], 1⟩, ⟨[(0, -1)], -2⟩]

theorem sys_accepted : farkasCheck sys [1, 1] = true := by decide
theorem sys_infeasible : sys ∈ Infeasible := farkasCheck_sound ⟨_, sys_accepted⟩
theorem negative_rejected : farkasCheck sys [-1, -1] = false := by decide
theorem short_rejected : farkasCheck sys [1] = false := by decide
theorem feasible_rejected : farkasCheck [⟨[(0, 1)], 1⟩, ⟨[(0, -1)], 0⟩] [1, 1] = false := by
  decide

end Silmaril.Logic.LinArith.Carrier.Examples
