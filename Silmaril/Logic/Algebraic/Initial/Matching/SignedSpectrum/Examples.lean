module

public import Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum.Thms
public import Silmaril.Logic.Algebraic.Initial.Quotient.Characterization.Examples

/-! Contextual collisions and unused empty-sort variables. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Presented Presented.Characterization

namespace Collision
abbrev source := Presented.Characterization.Examples.signature

/-- Keep the original empty theory; identify its two operations only in context. -/
def collapse : source ⟶ source where
  sorts := id
  ops op := match op with | .left => .left | .right => .left

theorem rejected (N : NativeModel source) :
    ¬ Satisfies N (spectrum Presented.Characterization.Examples.emptyTheory collapse) :=
  collision_rejects collapse Presented.Characterization.Examples.unrelated_constants rfl N
end Collision

namespace EmptySort
open Presented.Examples

theorem original_unrelated :
    ¬ Rel vacuousTheory (closedContext signature) left right := by
  intro h
  exact vacuous_constants_distinct (Quotient.sound h)

/-- The unused variable has no complete ground substitution; the compiler must
retain the negative upper-sort equality instead of closing that variable away. -/
theorem retains_negative :
    negative (𝟙 signature) left right ∈ spectrum vacuousTheory (𝟙 signature) :=
  negative_mem (𝟙 signature) original_unrelated

/-- The negative clause is actually satisfied by the independent separating
model's native expansion, rather than merely being listed syntactically. -/
theorem separating_satisfies_negative :
    (negative (𝟙 signature) left right).Satisfies
      (GuardedFOL.expand (structureOf separating)).base := by
  unfold negative
  rw [GuardedFOL.expanded_satisfaction, FOL.Sentence.holds_map]
  change ¬ (false = true)
  decide

/-- Padding raw carriers does not manufacture an active lower-sort value. -/
theorem lower_active_empty :
    IsEmpty ((decode (GuardedFOL.expand
      (structureOf (quotientModel vacuousTheory).obj))).carrier false) := by
  exact ⟨fun x => lower_empty.false
    (GuardedFOL.activeEquiv (structureOf (quotientModel vacuousTheory).obj) false x)⟩
end EmptySort

end Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum.Examples
