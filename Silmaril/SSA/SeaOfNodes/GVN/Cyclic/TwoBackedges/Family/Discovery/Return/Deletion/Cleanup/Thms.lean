module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup

open Diamond (ValueSort)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)
open Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup
  (first_some step_none step_checked step_shorter run_stops run_preserves)

variable {regs : List (ValueSort Unit)}
variable {p next : Program Opcode regs word}

theorem first?_eq_some_iff {index : Nat} :
    first? p = some index ↔
      index < p.header.length ∧ check p index = true ∧ ∀ j < index, check p j = false :=
  first_some

theorem step?_eq_none_iff :
    step? p = none ↔ ∀ index < p.header.length, check p index = false :=
  step_none

theorem step?_checked (found : step? p = some next) :
    ∃ index, first? p = some index ∧ delete? p index = some next :=
  step_checked found

theorem step?_shorter (found : step? p = some next) : next.header.length + 1 = p.header.length :=
  step_shorter found

/-- A full run exhausts the checked candidates in the current residual header. -/
theorem run_stops_of_fuel (fuel : Nat) (p : Program Opcode regs word) (enough : p.header.length ≤ fuel) :
    step? (run fuel p) = none :=
  run_stops fuel p enough

theorem optimize_saturated (p : Program Opcode regs word) :
    ∀ index < (optimize p).header.length, check (optimize p) index = false :=
  step?_eq_none_iff.mp (run_stops _ _ (Nat.le_refl _))

/-- The preheader, branch and return ports, and both feedback blocks are those of the redirected program. -/
theorem optimize_interface (p : Program Opcode regs word) :
    { optimize p with header := (Return.optimize p).header } = Return.optimize p :=
  (run_preserves _ _).1

/-- The activation result includes the selected occurrence and the complete feedback bank. -/
theorem optimize_step_of_arrives {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) : (optimize p).step model old = p.step model old :=
  ((run_preserves _ (Return.optimize p)).2.1 old).trans (Return.optimize_step_of_arrives p arrived)

theorem optimize_arrives_iff (p : Program Opcode regs word)
    (input old : Bank (regs := regs) model) (via : Incoming) (count : Nat) :
    (optimize p).Arrives model input via count old ↔ p.Arrives model input via count old :=
  ((run_preserves _ (Return.optimize p)).2.2.1 input via count old).trans (Return.optimize_arrives_iff p input old via count)

theorem optimize_run_eq (p : Program Opcode regs word) (budget : Nat) (input : Bank (regs := regs) model) :
    (optimize p).source.runFrom model budget 0 input = p.source.runFrom model budget 0 input :=
  ((run_preserves _ (Return.optimize p)).2.2.2 budget input).trans (Return.optimize_run_eq p budget input)

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup
