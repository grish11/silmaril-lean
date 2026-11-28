module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Branch.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch.Defs

/-! # A visible branch under a retained unary binder -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.BranchReplay.Example

open Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch (Op)

abbrev U : Ty Empty := .unit

def written : Region Op :=
  .let₁ .unit (.br 0 (.op .call (.var 1)))

def bound : Region Op :=
  .let₁ .unit (.let₁ (.op .call (.var 1)) (.br 0 (.var 0)))

def boundComposite : Region Op :=
  .let₁ .unit (.let₁ (.op .call .unit) (.br 0 (.var 0)))

def site : Paper.WithEntryLet.Site := .unaryBody .here

def replacement : Nat → Tm Op :=
  Tm.singleSubst .unit ∘ Silmaril.DeBruijn.lift Nat.succ

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.BranchReplay.Example
