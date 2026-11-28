module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Inverse.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Nested.Example.Defs

/-! # Invert the hoist of a captured sum below a let -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay.InverseExample

open Silmaril.DeBruijn (lift)
open SequencingObstruction (Instruction)
open Generators (weakenRows)
open Generators.Example (discriminator leftArm rightArm)
open NestedReplay.Example (outerRows)

def scopedRows : Fin 2 → Region Instruction :=
  fun j => (outerRows j).renameVars (lift Nat.succ)

def original : Region Instruction :=
  .let₁ .unit (.cfg (.case (discriminator.rename Nat.succ) leftArm rightArm) 2 scopedRows)

def hoisted : Region Instruction :=
  .let₁ .unit (.case (discriminator.rename Nat.succ)
    (.cfg leftArm 2 (weakenRows scopedRows)) (.cfg rightArm 2 (weakenRows scopedRows)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay.InverseExample
