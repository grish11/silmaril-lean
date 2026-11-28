module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Example.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Thms

/-! # A recurrent corrected square with a tagged state inclusion -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.ReplayExample

open CategoryTheory CategoryTheory.Limits
open EntryLetObstruction
open SequencingObstruction (Instruction)

abbrev Seed := Step (τ := Ty Empty) (Φ := Instruction)
abbrev X := Paper.TypeCategory.ofType (Φ := Instruction) U
abbrev D := Paper.TypeCategory.ofType (Φ := Instruction) (Silmaril.coprod U U)

noncomputable def embed : X ⟶ D := (Paper.TypeCategory.sumCofan U U).inl

noncomputable def retract : D ⟶ X :=
  (Paper.TypeCategory.sumIso U U).hom ≫ coprod.desc (𝟙 X) (𝟙 X)

/-- The two-transfer request is executed before returning to the source state. -/
noncomputable def source : X ⟶ X ⨿ X :=
  Paper.TypeCategory.ofRegion flatRequest_typed ≫ coprod.inr

/-- The moved request repeats, returning to the first tagged target state from either tag. -/
noncomputable def target : D ⟶ X ⨿ D :=
  retract ≫ Paper.TypeCategory.ofRegion movedRequest_typed ≫ embed ≫ coprod.inr

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.ReplayExample
