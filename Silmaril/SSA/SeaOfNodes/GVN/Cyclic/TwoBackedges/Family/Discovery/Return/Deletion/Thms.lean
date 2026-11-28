module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion

open Diamond (ValueSort)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)

variable {regs : List (ValueSort Unit)}
variable {p target : Program Opcode regs word} {index : Nat}

/-- Apart from the nominated write, the actual header assignments keep their original order. -/
theorem delete?_eq_some_iff :
    delete? p index = some target ↔ check p index = true ∧ target = erase p index :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.delete_eq_some p index

theorem delete?_shorter (accepted : delete? p index = some target) :
    target.header.length + 1 = p.header.length := by
  obtain ⟨safe, rfl⟩ := delete?_eq_some_iff.mp accepted
  exact Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.erase_count p index safe

/-- Preserve the chosen feedback occurrence and every field of the packet, or the observed return. -/
theorem delete?_step_eq (accepted : delete? p index = some target) (old : Bank (regs := regs) model) :
    target.step model old = p.step model old := by
  obtain ⟨safe, rfl⟩ := delete?_eq_some_iff.mp accepted
  exact Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.erase_step p index safe old

theorem delete?_arrives_iff (accepted : delete? p index = some target)
    (input old : Bank (regs := regs) model) (via : Incoming) (count : Nat) :
    target.Arrives model input via count old ↔ p.Arrives model input via count old := by
  obtain ⟨safe, rfl⟩ := delete?_eq_some_iff.mp accepted
  exact Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.erase_arrives
    p index safe input old via count

theorem delete?_run_eq (accepted : delete? p index = some target)
    (fuel : Nat) (input : Bank (regs := regs) model) :
    target.source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input := by
  obtain ⟨safe, rfl⟩ := delete?_eq_some_iff.mp accepted
  exact Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.erase_run p index safe fuel input

theorem afterReturn?_shape (accepted : afterReturn? p index = some target) :
    target = erase (Return.optimize p) index :=
  (delete?_eq_some_iff.mp accepted).2

theorem afterReturn?_shorter (accepted : afterReturn? p index = some target) :
    target.header.length + 1 = (Return.optimize p).header.length :=
  delete?_shorter accepted

theorem afterReturn?_step_of_arrives (accepted : afterReturn? p index = some target)
    {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) : target.step model old = p.step model old :=
  (delete?_step_eq accepted old).trans (Return.optimize_step_of_arrives p arrived)

theorem afterReturn?_arrives_iff (accepted : afterReturn? p index = some target)
    (input old : Bank (regs := regs) model) (via : Incoming) (count : Nat) :
    target.Arrives model input via count old ↔ p.Arrives model input via count old :=
  (delete?_arrives_iff accepted input old via count).trans (Return.optimize_arrives_iff p input old via count)

theorem afterReturn?_run_eq (accepted : afterReturn? p index = some target)
    (fuel : Nat) (input : Bank (regs := regs) model) :
    target.source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input :=
  (delete?_run_eq accepted fuel input).trans (Return.optimize_run_eq p fuel input)

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion
