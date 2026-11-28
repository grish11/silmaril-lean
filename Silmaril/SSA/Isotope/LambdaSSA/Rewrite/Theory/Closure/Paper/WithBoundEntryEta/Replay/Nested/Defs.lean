module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Defs

/-! # Hoist a nested entry at one address -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NestedReplay

open WithEntryLet (Site)

/-- Keep the inner CFG and redirect its outward exits through the outer
re-entry family. Label substitution keeps the inner labels local and
weakens the continuations under each inner row's value binder. -/
def hoistRoot {Φ : Type v} : Region Φ → Option (Region Φ)
  | .cfg (.cfg e m inner) _ outer =>
    some ((Region.cfg e m inner).lsubst (cfgEntryContinuations outer))
  | _ => none

/-- Apply the nested entry generator at one region address. -/
abbrev hoistAt {Φ : Type v} (site : Site) (r : Region Φ) : Option (Region Φ) :=
  site.rewriteAt hoistRoot r

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NestedReplay
