module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Defs

/-! # Bind the argument of one addressed branch -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.BranchReplay

open WithEntryLet (Site)

/-- Bind the argument at a branch, keeping the same destination. -/
def bindRoot {Φ : Type v} : Region Φ → Option (Region Φ)
  | .br i a => some (.let₁ a (.br i (.var 0)))
  | _ => none

/-- Apply the single branch-binding action at a region address. -/
abbrev bindAt {Φ : Type v} (site : Site) (r : Region Φ) : Option (Region Φ) :=
  site.rewriteAt bindRoot r

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.BranchReplay
