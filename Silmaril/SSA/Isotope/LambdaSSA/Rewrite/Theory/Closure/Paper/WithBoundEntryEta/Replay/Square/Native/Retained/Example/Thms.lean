module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Retained.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameExample

/-! # Native compatibility and the constructor boundary on a retained payload -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame.Retained.Example

open CategoryTheory CategoryTheory.Limits
open Paper.WithCaseReturns.BinaryFold (alternatingStep)
open SequencingObstruction (Instruction)
open Paper.TypeCategory (ConstructorReturn)

theorem update_square :
    alternatingStep g ≫ coprod.map (𝟙 B) (fold Bit) = fold Bit ≫ g :=
  fold_square update_guarded

/-- On a left payload one round flips the bit and two rounds restore it. -/
theorem single_doubled_ne : g ≠ g₂ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameExample.single_doubled_ne

theorem doubled_square :
    alternatingStep g₂ ≫ coprod.map (𝟙 B) (fold Bit) = fold Bit ≫ g₂ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameExample.doubled_square

/-- The alternating one-round source cannot have the doubled step as its
target under the same native payload fold. -/
theorem crossed_square_ne :
    alternatingStep g ≫ coprod.map (𝟙 B) (fold Bit) ≠ fold Bit ≫ g₂ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameExample.crossed_square_ne

/-- The exact fold of a retained bit has no constructor-return representative. -/
theorem no_constructor_fold : ¬ ConstructorReturn (fold (Φ := Instruction) Bit) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrameExample.no_constructor_fold

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame.Retained.Example
