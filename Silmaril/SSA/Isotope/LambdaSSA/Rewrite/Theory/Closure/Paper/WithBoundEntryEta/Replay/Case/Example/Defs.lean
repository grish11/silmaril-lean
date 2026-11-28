module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Example.Defs

/-! # A computed case entry with differently typed local labels -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay.Example

open Silmaril.DeBruijn (lift)
open SequencingObstruction (Instruction)
open Paper.EntryLetObstruction.Destructure (rows)
open Generators (weakenRows)
open Generators.Example (discriminator leftArm rightArm)

def original : Region Instruction := .cfg (.case discriminator leftArm rightArm) 2 rows

def hoisted : Region Instruction :=
  .case discriminator (.cfg leftArm 2 (weakenRows rows)) (.cfg rightArm 2 (weakenRows rows))

/-- Place the same redex below a binder, keeping the discriminator's
captured tagged input available for specialization. -/
def underBinder (r : Region Instruction) : Region Instruction := .let₁ .unit (r.renameVars Nat.succ)

def site : WithEntryLet.Site := .unaryBody .here

def specialize : Nat → Tm Instruction :=
  Tm.singleSubst (.inl (.var 0)) ∘ lift Nat.succ

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay.Example
