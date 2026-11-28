module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Defs

/-! # The addressed binary entry move -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta

open Silmaril.DeBruijn (lift)
open WithEntryLet (Site)

/-- Move a product destructuring out of a CFG and weaken its rows past
the two product captures. -/
def moveEntry₂ {Φ : Type v} : Region Φ → Option (Region Φ)
  | .cfg (.let₂ a body) n blocks =>
    some (.let₂ a (.cfg body n
      (fun j => ((blocks j).renameVars (lift Nat.succ)).renameVars (lift Nat.succ))))
  | _ => none

/-- Use the binary entry move at one region address. -/
abbrev move₂ {Φ : Type v} (site : Site) (r : Region Φ) : Option (Region Φ) :=
  site.rewriteAt moveEntry₂ r

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta
