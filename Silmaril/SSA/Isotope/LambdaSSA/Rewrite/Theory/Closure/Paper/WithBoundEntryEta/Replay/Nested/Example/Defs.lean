module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Nested.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Example.Defs

/-! # Nested hoisting through a value binder and a captured sum -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NestedReplay.Example

open Silmaril.DeBruijn (lift)
open SequencingObstruction (Instruction)
open Paper.EntryLetObstruction.Destructure (U entry rows)
open Generators.Example (Choice)

open Generators.Example (innerEntry innerRows nestedEntry)

/-- The second outer row reads the original tagged input below its
own payload, exercising both lifts in the re-entry family. -/
def outerRows : Fin 2 → Region Instruction :=
  Fin.cases (.br 1 (.pair (.var 0) .unit))
    (fun _ => .case (.var 1) (.br 2 (.var 0)) (.br 2 .unit))

def original : Region Instruction :=
  .let₁ .unit ((Region.cfg nestedEntry 2 outerRows).renameVars Nat.succ)

def hoisted : Region Instruction :=
  .let₁ .unit (Region.renameVars Nat.succ
    (.cfg (innerEntry.lsubst (liftLSubstN 1 (cfgEntryContinuations outerRows))) 1
      (fun j => (innerRows j).lsubst (liftLSubstVars (liftLSubstN 1 (cfgEntryContinuations outerRows))))))

def site : WithEntryLet.Site := .unaryBody .here

/-- Specialize the retained input to a left injection of a constructor variable. -/
def specialize : Nat → Tm Instruction :=
  Tm.singleSubst (.inl (.var 0)) ∘ lift Nat.succ

def emptyInner : Fin 0 → Region Instruction := Fin.elim0

/-- A separate native comparison witness with an empty inner label prefix. -/
def zeroInnerOriginal : Region Instruction :=
  .cfg (.cfg entry 0 emptyInner) 2 rows

def zeroInnerHoisted : Region Instruction :=
  .cfg (entry.lsubst (cfgEntryContinuations rows)) 0
    (fun j => (emptyInner j).lsubst (liftLSubstVars (cfgEntryContinuations rows)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NestedReplay.Example
