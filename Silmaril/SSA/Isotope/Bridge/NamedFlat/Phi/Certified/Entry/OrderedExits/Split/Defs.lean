module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Defs

/-! # Checked splitting at the ordered φ interface -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)

universe v w
variable {V W K J : Type w} {F : Type v} [DecidableEq K]

/-- Check the existing split rewrite in an ordered graph, whose external
labels are allowed to be `some key`. Require an actual header so the
forwarder cannot replace an external payload. Each typed admission checks
normalization in its own declared exit partition. -/
def checkSplit [DecidableEq V] [DecidableEq W] [DecidableEq J] [DecidableEq F]
    (plan : Plan V W K J) (original : Graph V K F) (split : Graph W J F) : Bool :=
  (original.blocks.lookup plan.header).isSome && plan.hasEdge original &&
    decide (split = plan.rewrite original)

structure CheckedSplit (plan : Plan V W K J) (original : Graph V K F) (split : Graph W J F) : Prop where
  header : (original.blocks.lookup plan.header).isSome = true
  edge : plan.hasEdge original = true
  rewritten : split = plan.rewrite original

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
