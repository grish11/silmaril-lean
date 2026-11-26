module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Defs

/-! # Search the physical preheader of one live origin before ranking blocks -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch

open Silmaril.MLIR.Arith (Width)

variable {Input extra : List Width} {saved carried result : Width}

/-- Try physical cuts from the end of the actual saved prefix through zero.
    Stop at the first cut whose typed splice succeeds for this identity. -/
def latest? (state : Layout.State Input saved carried result extra) (origin : Nat) :
    Option (Nat × Layout.Move state) :=
  (Layout.Discovery.Policy.latest.cuts state.savedCount).findSome? fun cut =>
    (Layout.emit? state ⟨origin, cut⟩).map (cut, ·)

/-- Supply the discovered cut to the existing checked ranker. Cut zero is
    already a checked refusal if the search exhausted the prefix. -/
def nomination (state : Layout.State Input saved carried result extra) (origin : Nat) : Nomination :=
  ⟨origin, ((latest? state origin).map Prod.fst).getD 0⟩

abbrev Ranked (state : Layout.State Input saved carried result extra) (origin : Nat) :=
  HeaderSplice.Walk.Ranked state (nomination state origin)

/-- Compare the bounded header walk with the latest accepted physical cut in
    the input preheader. Both alternatives are checked on the same input CFG. -/
def rank? (state : Layout.State Input saved carried result extra) (origin headerBudget : Nat) :
    Option (Ranked state origin) :=
  HeaderSplice.Walk.rank? state (nomination state origin) headerBudget

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch
