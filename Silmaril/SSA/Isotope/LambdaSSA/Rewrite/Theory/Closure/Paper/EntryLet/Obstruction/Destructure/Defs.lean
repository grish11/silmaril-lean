module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.SequencingObstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Defs

/-! # A computed pair followed by two differently typed local transfers -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction.Destructure

open SequencingObstruction (Instruction)

abbrev U : Ty Empty := .unit
abbrev P : Ty Empty := .product U U

/-- Entry-to-row transfers carry Unit, then Unit × Unit, in that order. -/
def labels : Fin 2 → Ty Empty := Fin.cases U (fun _ => P)

def rows : Fin 2 → Region Instruction :=
  Fin.cases (.br 1 (.pair (.var 0) .unit)) (fun _ => .br 2 .unit)

def initializer : Tm Instruction := .pair (.op .tick .unit) .unit

def entry : Region Instruction := .let₂ initializer (.br 0 (.var 1))

def original : Region Instruction := .cfg entry 2 rows

def reentered : Region Instruction :=
  entry.bindBranchArguments.lsubst (cfgEntryContinuations rows)

/-- Move the computed destructuring out of the two-label table. -/
def moved : Region Instruction :=
  .let₂ initializer (.cfg (.br 0 (.var 1)) 2 (fun j =>
    ((rows j).renameVars (Silmaril.DeBruijn.lift Nat.succ)).renameVars (Silmaril.DeBruijn.lift Nat.succ)))

/-- After the two local transfers, send the feedback state back to the loop. -/
def recurring (r : Region Instruction) : Region Instruction :=
  compLSubst (fun _ => r) (fun _ => .br 0 (.inr .unit)) 0

end Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction.Destructure
