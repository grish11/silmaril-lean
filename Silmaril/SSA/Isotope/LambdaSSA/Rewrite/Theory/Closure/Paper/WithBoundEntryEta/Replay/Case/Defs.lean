module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Defs

/-! # Hoist a case entry at one address -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay

open Generators (weakenRows)
open WithEntryLet (Site)

/-- Keep the discriminator in place and run the table inside the selected
arm, weakening each row past the arm payload. -/
def hoistRoot {Φ : Type v} : Region Φ → Option (Region Φ)
  | .cfg (.case a l r) n rows =>
    some (.case a (.cfg l n (weakenRows rows)) (.cfg r n (weakenRows rows)))
  | _ => none

abbrev hoistAt {Φ : Type v} (site : Site) (r : Region Φ) : Option (Region Φ) :=
  site.rewriteAt hoistRoot r

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay
