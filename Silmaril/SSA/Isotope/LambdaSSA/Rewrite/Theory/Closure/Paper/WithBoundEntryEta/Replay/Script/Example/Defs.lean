module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Example.Defs

/-! # Hoist a case, bind the left branch, then hoist that let -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ScriptReplay.Example

open Silmaril.DeBruijn (lift)
open SequencingObstruction (Instruction)
open Paper.EntryLetObstruction.Destructure (rows)
open Generators (weakenRows)
open Generators.Example (discriminator rightArm)
open CaseReplay.Example (underBinder)

def moves : List Move :=
  [.caseEntry (.unaryBody .here),
   .bindBranch (.unaryBody (.leftArm (.entry .here))),
   .unaryEntry (.unaryBody (.leftArm .here))]

def source : Region Instruction :=
  underBinder CaseReplay.Example.original

def target : Region Instruction :=
  let scopedRows := fun j => (rows j).renameVars (lift Nat.succ)
  .let₁ .unit (.case (discriminator.rename Nat.succ)
    (.let₁ (.var 0) (.cfg (.br 0 (.var 0)) 2 (weakenRows (weakenRows scopedRows))))
    (.cfg rightArm 2 (weakenRows scopedRows)))

/-- The two arms capture different free variables in their sole row. -/
def inverseTarget : Region Instruction :=
  .case (.inl .unit)
    (.cfg (.br 0 .unit) 1 (fun _ => .br 1 (.var 2)))
    (.cfg (.br 0 .unit) 1 (fun _ => .br 1 (.var 3)))

/-- After replacing both captures by Unit the two row tables coincide. -/
def closedPredecessor : Region Instruction :=
  .cfg (.case (.inl .unit) (.br 0 .unit) (.br 0 .unit)) 1 (fun _ => .br 1 .unit)

def forgetCaptures : Nat → Tm Instruction := fun _ => .unit

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ScriptReplay.Example
