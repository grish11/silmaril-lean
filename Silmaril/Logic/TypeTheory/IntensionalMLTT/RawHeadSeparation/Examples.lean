module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.Thms

public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.Examples

/-- Cumulativity still permits any strictly higher indexed universe in the original calculus. -/
theorem universe_three_in_five : Typing .nil (.univ 3) (.univ 5) :=
  typing_univ_iff.mpr ⟨⟨.nil⟩, by decide⟩

/-- Arbitrary raw conversion intermediates cannot make type-in-type derivable. -/
theorem no_type_in_type (i : ℕ) : ¬ Typing .nil (.univ i) (.univ i) :=
  not_typing_univ_self .nil

/-- The generic persistent-head result separates universes from primitive natural types too. -/
theorem universe_not_nat (i : ℕ) : ¬ Convertible (.univ i : Term 0) .nat :=
  not_convertible_of_rigidHead_ne rfl rfl (by intro h; cases h)

/-- No typing or formation assumption is required to separate product and sum heads. -/
theorem scoped_product_not_sum (A A' : Term 2) (B B' : Term 3) :
    ¬ Convertible (.pi A B) (.sigma A' B') :=
  not_convertible_pi_sigma A A' B B'

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.Examples
