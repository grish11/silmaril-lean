module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Retained.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.RetainedFrame
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameExample

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithBoundEntryEta.NativeFrame.Retained
open Paper.WithBoundEntryEta.NativeFrame.Retained.Example
open Paper.EntryLetObstruction (U)
open SequencingObstruction (Instruction)
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofRegion ofRegion_eq_iff sumIso ConstructorReturn)
open Paper.WithCaseReturns.BinaryFold (alternatingStep)

theorem single_doubled_ne : g ≠ g₂ := by
  intro he
  have eq := (single_eq (B := U) update_guarded).trans
    (he.trans (doubled_eq (B := U) update_guarded).symm)
  exact Sequencing.retained_rounds_ne
    ((ofRegion_eq_iff once_guarded twice_guarded).1 ((cancel_mono (sumIso U Bit).hom).1 eq))

theorem doubled_square :
    alternatingStep g₂ ≫ coprod.map (𝟙 B) (fold Bit) = fold Bit ≫ g₂ := by
  let round := CfgEta.TypeCategory.seqValueBranches update_guarded update_guarded
  have eq : single (B := U) round = g₂ :=
    (single_eq (B := U) round).symm.trans (doubled_eq (B := U) update_guarded)
  rw [← eq]
  exact fold_square round

theorem crossed_square_ne :
    alternatingStep g ≫ coprod.map (𝟙 B) (fold Bit) ≠ fold Bit ≫ g₂ :=
  fun h => single_doubled_ne ((fold_square_iff_single update_guarded g₂).mp h)

theorem no_constructor_fold : ¬ ConstructorReturn (fold (Φ := Instruction) Bit) := by
  rintro ⟨a, ha, he⟩
  have eq := (fold_eq_case (Φ := Instruction) Bit).symm.trans he
  exact Sequencing.retained_fold_ne_constructor ha
    ((ofRegion_eq_iff (foldRegion_guarded Bit) (.br (ℓ := 0) rfl ha)).1 eq)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameExample
