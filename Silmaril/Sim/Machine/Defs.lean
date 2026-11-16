module

public import Silmaril.Sim.Core.Defs
public import Silmaril.X86.RelIsa.Defs

/-!
# Bridges to Silmaril's machine models (header)

* `ofRelIsa A view`: a relational machine `Silmaril.X86.RelIsa σ` (explicit `stop`
  outcome) as a `Silmaril.Sim.Machine` with one command, its `ok`-steps as the step relation,
  and `relStop A` (the states that may stop) as the stop predicate of `Machine.Must`.

`Thms`: `must_ofRelIsa_iff` (`Machine.Must` on `ofRelIsa` is `RelIsa.Must`) and
`relIsaMust_of_coSimulation` (demonic total correctness of the reference from that of a
complete simulator), the shape of `Silmaril.Problems.FnCorrect`.
-/

@[expose] public section

namespace Silmaril.Sim

open Silmaril.X86 (RelIsa)

variable {σ L V : Type}

/-- A relational machine as a one-command machine (its `ok`-steps). -/
def ofRelIsa (A : RelIsa σ) (view : σ → PState L V) : Machine Unit L V :=
  ⟨σ, view, fun _ s t => A.step s (.ok t)⟩

/-- The states of a relational machine that may stop. -/
def relStop (A : RelIsa σ) (s : σ) : Prop := A.step s .stop

end Silmaril.Sim

end
